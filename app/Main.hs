{-# LANGUAGE OverloadedLabels, OverloadedStrings, ViewPatterns, NamedFieldPuns, RecordWildCards, TemplateHaskell, LambdaCase, TupleSections, Rank2Types, MultiWayIf, TypeSynonymInstances, FlexibleInstances #-}

import qualified Data.Set as S
import Data.Text ( Text(..) )
import qualified Data.Text as T
import qualified Data.Text.Encoding as TE
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.Encoding as TLE
import qualified Data.Array as A
import qualified Data.Map.Strict as M
import qualified Data.ByteString.UTF8 as UB
import qualified Data.ByteString.Lazy.UTF8 as UBL
import qualified Data.ByteString.Lazy.Char8 as C8L
import qualified Data.ByteString.Lazy as BL
import qualified Data.Aeson as Aeson
import qualified Data.Csv as CSV

import Data.Char ( toLower, isAlphaNum, ord )
import Control.Arrow ( (***), (&&&), first, second )
import Control.Exception ( Exception(..), throw )
import Control.Applicative ( (<|>), Alternative(..) )
import Control.Monad ( void, zipWithM )
import Data.List ( partition )
import Data.Data ( showConstr, Data(..) )
import Data.Foldable ( foldrM )
import System.Environment ( getArgs )
import Control.Lens ( makeLenses )
import qualified Control.Lens as L
import Control.Lens.Operators
import Control.Monad.State.Strict ( MonadState(..), gets, lift )
import Control.Monad.Trans.State.Strict ( StateT(..), execState, evalState )

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

-- -- -- HasBOLT
-- import Data.Default ( Default(..) )
-- import Database.Bolt ( (=:) )
-- import qualified Database.Bolt as Bolt
-- -- import Database.Bolt.Extras
-- import Database.Bolt.Extras.DSL

import System.IO ( openFile, hClose, hPutStrLn, hPutStr, Handle(..), IOMode(..) )

-- 
import Lib

import Debug.Trace ( trace )

-- querya_ = Bolt.query_ . tracethru
-- querya = Bolt.query . tracethru

tracethru :: Show a => a -> a
tracethru s = trace (show s) s

data ASTState = ASTState {
  _ast_nodeid :: Int
  , _ast_keys :: M.Map T.Text Handle -- label -> node file
}
makeLenses ''ASTState
data Field = I Int | F Float | S T.Text
instance CSV.ToField Field where
  toField = \case
    I i -> CSV.toField i
    F f -> CSV.toField f
    S s -> CSV.toField s

class Fieldable a where
  mkField :: a -> Field

instance Fieldable Integer where
  mkField = I . fromIntegral
  
instance Fieldable Int where
  mkField = I
  
instance Fieldable Float where
  mkField = F
  
instance Fieldable Double where
  mkField = F . realToFrac
  
instance Fieldable Rational where
  mkField = F . fromRational
  
instance Fieldable UB.ByteString where
  mkField = S . TE.decodeUtf8
  
instance {-# OVERLAPS #-} Fieldable String where
  mkField = S . T.pack

instance {-# OVERLAPPABLE #-} Fieldable f => Fieldable [f] where
  mkField = S . T.stripEnd . TL.toStrict . TLE.decodeUtf8 . CSV.encodeWith opts . pure . map mkField
    where
      opts = CSV.defaultEncodeOptions {
        CSV.encDelimiter = fromIntegral $ ord '|'
      }

instance Fieldable Text where
  mkField = S

field2neo4j_ty :: Field -> T.Text
field2neo4j_ty = \case
  I _ -> ":INT"
  F _ -> ":FLOAT"
  S _ -> ":STRING"

modifyM :: MonadState s m => (s -> m s) -> m ()
modifyM f = do
  old <- get
  new <- f old
  put new

type ASTStateT a = StateT ASTState IO a
ast_node :: T.Text -> [(T.Text, Field)] -> ASTStateT Int
ast_node label params_raw = do
  -- TODO rels don't have IDs
  -- TODO alternatively, partition this function into common parts and make node + rel separate functions (since :ID has special treatment but :START_ID and :END_ID don't)
  -- I do have to make it distinct, in the state too, because the files need to be distinguished
  
  let (magic_params, params) =
        both M.fromList
        $ first (map (first (magic_keys M.!)))
        $ partition ((`M.member` magic_keys) . fst) params_raw
      magic_keys :: M.Map T.Text T.Text
      magic_keys = M.fromList [
          ("idx", ":ID")
          , ("start_˙id", ":START_ID")
          , ("end_id", ":END_ID")
        ]
  
  -- NOTE this isn't lazy in incrementing, it always increments. That's kind of okay for now, but is truly a bit wasteful... the alternative is a case statement or MaybeT
  -- magic_params' <- M.alterF (\mx -> runMaybeT $ do
  --     MaybeT $ pure mx -- no wait i want the opposite of this
  --     lift $ I <$> (ast_nodeid <<%= (+1))
  --   ) ":ID" magic_params
  magic_params' <- M.alterF (\mx -> case mx of
      Just x -> pure mx
      Nothing -> (Just . I) <$> (ast_nodeid <<%= (+1))
    ) ":ID" magic_params
    
  let new_file = do
        h' <- lift (openFile ("tmp/" ++ filter isAlphaNum (T.unpack label)) WriteMode)
        -- write header
        lift $ BL.hPut h' $ CSV.encode $ pure $ 
          ":LABEL"
          : M.keys magic_params'
          ++ map (uncurry T.append . second field2neo4j_ty) (M.toAscList params)
        return h'
  modifyM (ast_keys %%~ M.alterF (\mv -> case mv of
      Just v -> pure mv
      Nothing -> Just <$> new_file
    ) label) -- man what a minefield. I just want to take the state and return a transformation done in the corresponding monad to that state, in a compact and idiomatic way. The `ast_keys %%~` is the right way to modify the state to produce an `m s`, but this is not exactly a lens
        -- %= (M.insert label h')
  ksets' <- gets (^. ast_keys)
  lift $ BL.hPut (ksets' M.! label) $ CSV.encode $ pure $
    (S label)
    : M.elems magic_params'
    ++ M.elems params -- assumes the list keys for all labels are identical, TODO make this more robust rather than this implicit equality (although it requires buffering the whole set of entries in case the keys change, or one file per label-keyset combination)
  return $ (\(I i) -> i) $ magic_params' M.! ":ID" -- meeeeeh.
  

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

(=:) :: Fieldable b => a -> b -> (a, Field)
a =: b = (a, mkField b)

span2props pre sp = [
    (pre `T.append` "sp_fn") =: unpackFS (srcSpanFile sp)
    , (pre `T.append` "sp_l0") =: srcSpanStartLine sp
    , (pre `T.append` "sp_ch0") =: srcSpanStartCol sp
    , (pre `T.append` "sp_lf") =: srcSpanEndLine sp
    , (pre `T.append` "sp_chf") =: srcSpanEndCol sp
  ]

scope2props pre scope =
  ((pre `T.append` "scope") =: datactor2text scope)
  : (case scope of
    LocalScope sp -> span2props (pre `T.append` "scope_") sp
    _ -> [])

-- recs2id recs ident =
--   let ident' = "id(" `T.append` ident `T.append` ")"
--   in case recs of
--     rec:_ -> rec `Bolt.at` ident'
--     _ -> throw $ Bolt.RecordHasNoKey ident'

ast2cypher :: FilePath -> FilePath -> HieAST TypeIndex -> ASTStateT Int -- Bolt.BoltActionT IO Int -- IO ()
ast2cypher hs_path hie_path (Node {..}) = do
    let (ann_ctors, ann_tys) = both (map unpackFS) $ unzip $ S.toList $ nodeAnnotations nodeInfo -- S.toList $ S.map (("annotations" =:) . T.pack . UBL.toString . Aeson.encode . both unpackFS)
        -- (sp_fn, sp_l0, sp_ch0, sp_lf, sp_chf) = flat_realsrcspan nodeSpan
        sp_props = span2props "" nodeSpan
    ast_idx <- ast_node "GraphieAST" (
        ("ann_ctors" =: ann_ctors)
        : ("ann_tys" =: ann_tys)
        : sp_props
      )
    
    -- type relationships
    _ <- mapM (\(idx, ty) -> do
        ty_idx <- ast_node "GraphieTy" [
            "idx" =: ty
            , "path" =: T.pack hie_path
          ]
        _ty_rel <- ast_node "GRAPHIE_AST2TY" [
            "pos" =: idx,
            "start_id" =: ast_idx,
            "end_id" =: ty_idx
          ]
        pure ()
      ) (zip ([0..] :: [Int]) $ nodeType nodeInfo)
    
    -- context relationships and misc
    _ <- mapM (\(ident, (IdentifierDetails {..})) -> do
        let ident_props = case ident of
              Left name -> ["con" =: T.pack "Name", "name" =: uniquable2text name]
              Right modname -> ["con" =: T.pack "ModuleName", "name" =: uniquable2text modname]
        
        ident_idx <- ast_node "GraphieIdent" ident_props
        
        _ <- mapM (\ctx -> do
            ctx_idx <- ctxinfo2cypher ctx
            ast_node "GRAPHIE_AST2CTX" [
                "start_id" =: ast_idx
                , "end_id" =: ctx_idx
              ]
          ) (S.toList identInfo)
        
        case identType of
          Just ty -> do
            ident_ty_idx <- ast_node "GraphieTy" ["idx" =: ty, "path" =: T.pack hie_path]
            void $ ast_node "GRAPHIE_IDENT2TY" [
                "start_id" =: ident_idx
                , "end_id" =: ident_ty_idx
              ]
          Nothing -> pure ()
      ) (M.assocs (nodeIdentifiers nodeInfo))
    
    next_idxs <- mapM (ast2cypher hs_path hie_path) nodeChildren
    _ <- (flip (`zipWithM` ([0..] :: [Int])) next_idxs) $ \pos next_idx -> ast_node "GRAPHIE_AST2AST" ["pos" =: pos, "start_id" =: ast_idx, "end_id" =: next_idx]
      
    return ast_idx
    
  where -- TODO refine encapsulations
    mk_ctx_query con props = ast_node "GraphicCtx" (
        ("con" =: T.pack con)
        : ("path" =: T.pack hie_path)
        : props
      )
    -- ctxinfo2cypher :: NodeSelector -> ContextInfo -> Free Expr ()
    ctxinfo2cypher = \case
      Use -> mk_ctx_query "Use" []
      MatchBind -> mk_ctx_query "MatchBind" []
      IEThing ty -> mk_ctx_query "MatchBind" ["ietycon" =: T.pack (show ty)]
      TyDecl -> mk_ctx_query "MatchBind" []
      ValBind bindty bindscope m_bindspan -> mk_ctx_query "ValBind" $
          ["bindtycon" =: T.pack (show bindty)]
          ++ (case m_bindspan of
              Just sp -> span2props "bind_" sp
              Nothing -> [])
          ++ scope2props "" bindscope
      PatternBind patscope outscope m_bindspan -> mk_ctx_query "PatternBind" $
        (case m_bindspan of
            Just sp -> span2props "bind_" sp
            Nothing -> [])
        ++ scope2props "pat_" patscope
        ++ scope2props "out_" outscope
      ClassTyDecl m_bindspan -> mk_ctx_query "ClassTyDecl" $ case m_bindspan of
        Just sp -> span2props "bind_" sp
        Nothing -> []
      Decl declty m_bindspan -> mk_ctx_query "ClassTyDecl" $
        ["decltycon" =: show declty]
        ++ (case m_bindspan of
          Just sp -> span2props "bind_" sp
          Nothing -> [])
      TyVarBind declscope tyvarscope -> mk_ctx_query "PatternBind" $ -- `declscope` as a name is just a guess, not really sure what that first arg is
        scope2props "" declscope
        -- TODO the rest, good luck :S
        -- ++ (case tyvarscope of
        --   ResolvedScopes scopes -> )
      RecField ctx m_bindspan -> mk_ctx_query "RecField" $
        ["ctxtycon" =: T.pack (show ctx)]
        ++ (case m_bindspan of
          Just sp -> span2props "bind_" sp
          Nothing -> [])

uniquable2text :: Uniquable s => s -> Text
uniquable2text = T.pack . show . getUnique

datactor2text :: Data d => d -> Text
datactor2text = T.pack . showConstr . toConstr 

types2cypher :: Traversable t => FilePath -> t (TypeIndex, HieTypeFlat) -> ASTStateT () -- Bolt.BoltActionT IO ()
types2cypher path tys = do
  -- insert nodes first
  mapM (\(idx, ty) -> case ty of
      HTyVarTy (uniquable2text -> name) -> mk_ty_query idx "TyVarTy" ["name" =: name]
      HAppTy _t0 _targs -> mk_ty_query idx "AppTy" []
      HTyConApp (IfaceTyCon { ifaceTyConName = (uniquable2text -> name) }) _targs -> mk_ty_query idx "TyConApp" ["name" =: name]
      HForAllTy _ _ -> mk_ty_query idx "ForAllTy" []
      HFunTy tyarg tyret -> mk_ty_query idx "FunTy" []
      HQualTy tyctx tyret -> mk_ty_query idx "FunTy" []
      HLitTy tylit -> mk_ty_query idx "HLitTy" [
        case tylit of
          IfaceNumTyLit num -> "value" =: num
          IfaceStrTyLit fs -> "value" =: unpackFS fs
        ]
      HCastTy ty -> mk_ty_query idx "CastTy" []
      HCoercionTy -> mk_ty_query idx "CoercionTy" []
    ) tys
  -- then insert relationships
  -- TODO maybe make a monad/transformer to sort these into the right order
  void $ mapM (\(idx, ty) -> case ty of
      HAppTy t0 (HieArgs tn) -> mk_args_query t0 tn
      HTyConApp _ (HieArgs tn) -> mk_args_query idx tn -- (IfaceTyCon { ifaceTyConName = (uniquable2text -> name) })
      HForAllTy ((name, ty0), argflag) ty1 -> mk_ty_rel ty0 ty1 ["name" =: uniquable2text name, "argflag" =: datactor2text argflag]
      HFunTy tyarg tyret -> do
        mk_ty_rel idx tyarg ["pos" =: (0 :: Int)]
        mk_ty_rel idx tyret ["pos" =: (1 :: Int)]
      HQualTy tyctx tyret -> do
        mk_ty_rel idx tyctx ["pos" =: (0 :: Int)]
        mk_ty_rel idx tyret ["pos" =: (1 :: Int)]
      HCastTy ty -> mk_ty_rel idx ty []
      _ -> pure ()
    ) tys
  where -- TODO optimize by reusing labelled nodes (return from these query ctors) -- TODO clean up encapsulations (e.g. closure over `path` is a bit arbitrary and loose)
    mk_ty_query idx con props = ast_node "GraphieTy" (
        ("con" =: T.pack con)
        : ("path" =: T.pack path)
        : ("idx" =: idx)
        : props
      )
    mk_args_query t0 tn = void $ mapM (\(argpos, (_argvisible, argt)) -> mk_ty_rel t0 argt ["pos" =: argpos]) (zip ([0..] :: [Int]) tn) -- LOSS _argvisible
    -- TODO URGENT path used to be used to discriminate between type vars of differing paths, this needs to be re-introduced as a query against the state. All the IDs need to be remapped... damn this is a pain.
    mk_ty_rel tya_idx tyb_idx relprops = void $ ast_node "GRAPHIE_TY_REL" (
          "path" =: T.pack path
          : "start_id" =: tya_idx
          : "end_id" =: tyb_idx
          : relprops
        )
      -- -- make the relationship undirected:
      -- ast_node "GRAPHIE_TY_REL" (
      --     "path" =: T.pack path
      --     : "end_idx" =: tya
      --     : "start_idx" =: tyb
      --     : relprops
      --   )

-- hiefile_props :: HieFile -> [(Text, Bolt.Value)]
hiefile_props (HieFile {..}) = [
    "hs_file" =: T.pack hie_hs_file
    , "hie_module" =: uniquable2text hie_module
  ]

main :: IO ()
main = do
  dflags <- dynFlagsForPrinting
  nc <- makeNc
    
  do
    dhies <- getArgs -- TODO switch to glob-based
    fhies <- fmap concat $ mapM getHieFilesIn $ dhies
    _ <- foldrM (\path nc' -> do
        (hie_file_result -> hie, nc'') <- readHieFile nc' path
        putStrLn path
        
        (`runStateT` (ASTState 0 mempty)) $ do
          -- base file
          hie_file_idx <- ast_node "GraphieHieFile" (hiefile_props hie)
          -- types
          types2cypher path (A.assocs $ hie_types hie)
          -- TODO exported names
          -- i.e. exports2cypher (hie_exports hie)
          -- ASTs
          ast_ids <- mapM (\(fs_name, ast) -> ast2cypher (unpackFS fs_name) path ast) (M.assocs $ getAsts $ hie_asts hie)
          
          (`mapM` ast_ids) $ \ast_idx -> 
            ast_node "GRAPHIE_FILE2AST" [
                "start_id" =: hie_file_idx
                , "end_id" =: ast_idx 
              ]
        return nc''
      ) nc fhies
    pure ()