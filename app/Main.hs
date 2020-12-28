{-# LANGUAGE OverloadedLabels, OverloadedStrings, ViewPatterns, NamedFieldPuns, RecordWildCards, TemplateHaskell, LambdaCase, TupleSections, Rank2Types, MultiWayIf #-}

import qualified Data.Set as S
import Data.Text ( Text(..) )
import qualified Data.Text as T
import qualified Data.Array as A
import qualified Data.Map.Strict as M
import qualified Data.ByteString.UTF8 as UB
import qualified Data.ByteString.Lazy.UTF8 as UBL
import qualified Data.Aeson as Aeson

import Control.Arrow ( (***), (&&&), first, second )
import Control.Monad ( void )
import Data.Data ( showConstr, Data(..) )
import Data.Foldable ( foldrM )
import System.Environment ( getArgs )

-- GHC
import SrcLoc ( SrcLoc(..), SrcSpan, RealSrcSpan(..), mkSrcLoc, mkSrcSpan, containsSpan, mkRealSrcSpan, mkRealSrcLoc, realSrcSpanStart, realSrcSpanEnd, srcSpanStartLine, srcSpanStartCol, srcSpanEndLine, srcSpanEndCol )
import Name ( nameOccName, nameModule_maybe, Name(..) )
import GHC ( moduleNameString, moduleName, ModuleName(..) )
import OccName ( occNameString )
import FastString ( FastString(..), fsLit, unpackFS )
import Data.Text.IO ( readFile )
import Text.Read ( readMaybe )
import SysTools ( initSysTools )
import DynFlags ( DynFlags, defaultDynFlags )
import Unique ( Uniquable(..), Unique(..) )
import IfaceType ( IfaceTyLit(..), IfaceTyCon(..) )

-- prof & HIE
import qualified GHC.Prof as Prof
import HieBin
import HieTypes
import HieUtils

-- HasBOLT
import Data.Default ( Default(..) )
import Database.Bolt ( (=:) )
import qualified Database.Bolt as Bolt
-- import Database.Bolt.Extras
import Database.Bolt.Extras.DSL

-- 
import Lib

import Debug.Trace ( trace )

querya_ = Bolt.query_ -- . tracethru
querya = Bolt.query -- . tracethru

tracethru :: Show a => a -> a
tracethru s = trace (show s) s
    
-- ppr_ast_node :: DynFlags -> HieAST a -> String
-- ppr_ast_node d = ppr_safe d . ((nodeAnnotations &&& M.map (identInfo) . nodeIdentifiers) . nodeInfo &&& nodeSpan)

-- ppr_ast :: DynFlags -> HieAST a -> String
-- ppr_ast d = uncurry ((++) . (++"\n")) . (ppr_ast_node d &&& unlines . map (unlines . map (' ':) . lines . ppr_ast d) . nodeChildren)

flat_realsrcspan :: RealSrcSpan -> (FastString, Int, Int, Int, Int)
flat_realsrcspan sp = (
    srcSpanFile sp
    , srcSpanStartLine sp
    , srcSpanStartCol sp
    , srcSpanEndLine sp
    , srcSpanEndCol sp
  )

span2props pre sp = [
    (pre `T.append` "sp_fn") =: unpackFS (srcSpanFile sp)
    , (pre `T.append` "sp_l0") =: srcSpanStartLine sp
    , (pre `T.append` "sp_ch0") =: srcSpanStartCol sp
    , (pre `T.append` "sp_lf") =: srcSpanEndLine sp
    , (pre `T.append` "sp_chf") =: srcSpanEndCol sp
  ]

scope2props pre scope =
  ((pre `T.append` "scope") =: showConstr (toConstr scope))
  : (case scope of
    LocalScope sp -> span2props (pre `T.append` "scope_") sp
    _ -> [])

ast2cypher :: Bolt.Pipe -> FilePath -> HieAST TypeIndex -> Bolt.BoltActionT IO Int -- IO ()
ast2cypher neop path (Node {..}) = do
    let (ann_ctors, ann_tys) = both (map unpackFS) $ unzip $ S.toList $ nodeAnnotations nodeInfo -- S.toList $ S.map (("annotations" =:) . T.pack . UBL.toString . Aeson.encode . both unpackFS)
        -- (sp_fn, sp_l0, sp_ch0, sp_lf, sp_chf) = flat_realsrcspan nodeSpan
        sp_props = span2props "" nodeSpan
    ((!! "id(n)") -> I this_id) <- querya $ formQuery $ do -- TODO URGENT this pattern match is dangerous; make into exception to rollback transaction upon pat match failure
      mergeF [PS $ P $ (#n .: "GraphieAST" .# (("ann_ctors" =: ann_ctors) : ("ann_tys" =: ann_tys) : sp_props))]
      _ <- mapM (\(idx, ty) -> do
          let tynode = withIdentifier (T.pack $ "ty" ++ show idx) defN
          withF ["n"]
          matchF [PS $ P $ tynode .: "GraphieTy" .# ["idx" =: ty]]
          mergeF [PS $ (#n -: (defR .: "GRAPHIE_AST2TY" .# ["pos" =: idx]) :!->: tynode)]
        ) (zip ([0..] :: [Int]) $ nodeType nodeInfo)
      _ <- mapM (\(idx, (ident, (IdentifierDetails {..}))) -> do
          let ident_ident = "ident_" ++ show idx
              ident_node = withIdentifier (T.pack ident_ident) defN
              ident_props = case ident of
                Left name -> ["con" =: T.pack "Name", "name" =: uniquable2text name]
                Right modname -> ["con" =: T.pack "ModuleName", "name" =: uniquable2text modname]
          mergeF [PS $ P $ ident_node .: "GraphieIdent" .# ident_props]
          _ <- mapM (\(ctx_idx, ctx) -> do
              let ctxnode = withIdentifier (T.pack $ "ctx" ++ (show ctx_idx) ++ "_" ++ ident_ident) defN
              ctxinfo2cypher ctxnode ctx
              mergeF [PS $ (#n -: (defR .: "GRAPHIE_AST2CTX") :!->: ctxnode)]
            ) (zip [0..] $ S.toList identInfo)
          case identType of
            Just ty -> do
              let ident_ty_node = withIdentifier (T.pack $ "ty_" ++ ident_ident) defN
              withF ["n", T.pack ident_ident]
              matchF [PS $ P $ ident_node .: "GraphieTy" .# ["idx" =: ty]]
              mergeF [PS $ ident_node -: (defR .: "GRAPHIE_IDENT2TY") :!->: ident_ty_node]
            Nothing -> pure ()
        ) (zip [0..] $ M.assocs (nodeIdentifiers nodeInfo))
      returnF ["id(n)"] -- hard for me to overstate how important this is
      
    next_id <- mapM (ast2cypher neop path) nodeChildren
    _ <- querya $ formQuery $ do
      matchF [PS $ P #n]
      matchF [PS $ P #m]
      whereF $ (ID "n" this_id) :&&: (ID "m" this_id)
      mergeF [PS $ #n -: (defR .: "GRAPHIE_AST2AST") :!->: #m]
      
    return this_id
    
  where -- TODO refine encapsulations
    mk_ctx_query node con props = mergeF [ -- TODO merge with mk_ty_query, unified by props and label
      PS $ P $ node
        .: "GraphieCtx"
        .# (
            ("con" =: T.pack con)
            : ("path" =: T.pack path)
            : props
          )
      ]
    -- ctxinfo2cypher :: NodeSelector -> ContextInfo -> Free Expr ()
    ctxinfo2cypher node = \case
      Use -> mk_ctx_query node "Use" []
      MatchBind -> mk_ctx_query node "MatchBind" []
      IEThing ty -> mk_ctx_query node "MatchBind" ["ietycon" =: T.pack (show ty)]
      TyDecl -> mk_ctx_query node "MatchBind" []
      ValBind bindty bindscope m_bindspan -> mk_ctx_query node "ValBind" $
          ["bindtycon" =: T.pack (show bindty)]
          ++ (case m_bindspan of
              Just sp -> span2props "bind_" sp
              Nothing -> [])
          ++ scope2props "" bindscope
      PatternBind patscope outscope m_bindspan -> mk_ctx_query node "PatternBind" $
        (case m_bindspan of
            Just sp -> span2props "bind_" sp
            Nothing -> [])
        ++ scope2props "" patscope
        ++ scope2props "" outscope
      ClassTyDecl m_bindspan -> mk_ctx_query node "ClassTyDecl" $ case m_bindspan of
        Just sp -> span2props "bind_" sp
        Nothing -> []
      Decl declty m_bindspan -> mk_ctx_query node "ClassTyDecl" $
        ["decltycon" =: show declty]
        ++ (case m_bindspan of
          Just sp -> span2props "bind_" sp
          Nothing -> [])
      TyVarBind declscope tyvarscope -> mk_ctx_query node "PatternBind" $ -- `declscope` as a name is just a guess, not really sure what that first arg is
        scope2props "" declscope
        -- TODO the rest, good luck :S
        -- ++ (case tyvarscope of
        --   ResolvedScopes scopes -> )
      RecField ctx m_bindspan -> mk_ctx_query node "RecField" $
        ["ctxtycon" =: T.pack (show ctx)]
        ++ (case m_bindspan of
          Just sp -> span2props "bind_" sp
          Nothing -> [])

uniquable2text :: Uniquable s => s -> Text
uniquable2text = T.pack . show . getUnique

types2cypher :: Foldable t => FilePath -> t (TypeIndex, HieTypeFlat) -> Bolt.BoltActionT IO ()
types2cypher path tys = do
  -- insert nodes first
  foldrM (\(idx, ty) () -> case ty of
      HTyVarTy (uniquable2text -> name) -> mk_ty_query idx "TyVarTy" ["name" =: name]
      HAppTy _t0 _targs -> mk_ty_query idx "AppTy" []
      HTyConApp (IfaceTyCon { ifaceTyConName = (uniquable2text -> name) }) _targs -> mk_ty_query idx "TyConApp" ["name" =: name]
      HForAllTy _ _ -> pure () -- TODO
      HFunTy tyarg tyret -> mk_ty_query idx "FunTy" []
      HQualTy tyctx tyret -> mk_ty_query idx "FunTy" []
      HLitTy tylit -> mk_ty_query idx "HLitTy" [
        case tylit of
          IfaceNumTyLit num -> "value" =: num
          IfaceStrTyLit fs -> "value" =: unpackFS fs
        ]
      HCastTy ty -> mk_ty_query idx "CastTy" []
      HCoercionTy -> mk_ty_query idx "CoercionTy" []
    ) () tys
  -- then insert relationships
  -- TODO maybe make a monad/transformer to sort these into the right order
  foldrM (\(idx, ty) () -> case ty of
      HAppTy t0 (HieArgs tn) -> mk_args_query t0 tn
      HTyConApp _ (HieArgs tn) -> mk_args_query idx tn -- (IfaceTyCon { ifaceTyConName = (uniquable2text -> name) })
      HForAllTy _ _ -> pure () -- TODO
      HFunTy tyarg tyret -> do
        mk_ty_rel idx tyarg ["pos" =: (0 :: Int)]
        mk_ty_rel idx tyret ["pos" =: (1 :: Int)]
      HQualTy tyctx tyret -> do
        mk_ty_rel idx tyctx ["pos" =: (0 :: Int)]
        mk_ty_rel idx tyret ["pos" =: (1 :: Int)]
      HCastTy ty -> mk_ty_rel idx ty []
      _ -> pure ()
    ) () tys
  where -- TODO optimize by reusing labelled nodes (return from these query ctors) -- TODO clean up encapsulations (e.g. closure over `path` is a bit arbitrary and loose)
    mk_ty_query idx con props = querya_ $ formQuery $ mergeF [
      PS $ P $ defN .: "GraphieTy"
                .# (
                    ("con" =: T.pack con)
                    : ("path" =: T.pack path)
                    : ("idx" =: idx)
                    : props
                  )
      ]
    mk_args_query t0 tn = foldrM (\(argpos, (_argvisible, argt)) () -> mk_ty_rel t0 argt ["pos" =: argpos]) () (zip ([0..] :: [Int]) tn) -- LOSS _argvisible
    mk_ty_rel tya tyb relprops = querya_ $ formQuery $ do
      matchF [
        PS $ P $ #a .: "GraphieTy"
                    .# ["path" =: T.pack path, "idx" =: tya],
        PS $ P $ #b .: "GraphieTy"
                    .# ["path" =: T.pack path, "idx" =: tyb]
        ]
      mergeF [PS $ (#a -: (defR .: "GRAPHIE_TY_REL" .# relprops) :!->: (#b))]

hiefile_props :: HieFile -> [(Text, Bolt.Value)]
hiefile_props (HieFile {..}) = [
    "hs_file" =: T.pack hie_hs_file
    , "hie_module" =: uniquable2text hie_module
  ]

main :: IO ()
main = do
  dflags <- dynFlagsForPrinting
  nc <- makeNc
  neop <- Bolt.connect def {
      Bolt.user = "neo4j",
      Bolt.password = "postgres"
      -- secure = True
    }
  dhies <- getArgs -- TODO switch to glob-based
  fhies <- fmap concat $ mapM getHieFilesIn $ dhies
  _ <- foldrM (\path nc' -> do
      (hie_file_result -> hie, nc'') <- readHieFile nc' path
      Bolt.run neop $ Bolt.transact $ do
        -- base file
        querya $ formQuery $ mergeF [PS $ P $ defN .: "GraphieHieFile" .# hiefile_props hie]
        -- types
        types2cypher path (A.assocs $ hie_types hie)
        -- TODO exported names
        -- i.e. exports2cypher (hie_exports hie)
        foldrM (\(fs_name, ast) () -> ast2cypher neop (unpackFS fs_name) ast) () (M.assocs $ getAsts $ hie_asts hie)
      return nc''
    ) nc fhies
  pure ()