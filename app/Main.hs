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
import Control.Monad ( void, zipWithM, join )
import Data.List ( partition, intersperse )
import Data.Maybe ( fromMaybe )
import Data.Bitraversable ( bisequence )
import Data.Data ( showConstr, Data(..) )
import Data.Foldable ( foldrM )
import System.Environment ( getArgs )
import Control.Lens ( makeLenses )
import qualified Control.Lens as L
import Control.Lens.Operators
import Control.Monad.State.Strict ( MonadState(..), gets, lift )
import Control.Monad.Trans.State.Strict ( StateT(..), execStateT, evalStateT, runStateT )

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

data EntityType = Neo4JNode | Neo4JRelationship
-- core state, counting node IDs and managing file handles
data ASTState = ASTState {
  _ast_nodeid :: Int
  , _ast_keys :: M.Map T.Text (EntityType, M.Map (S.Set T.Text) (Handle, T.Text)) -- label -> (entity type, params) -> node file; the second map is because some nodes have optional params that others omitted
}
makeLenses ''ASTState

-- outer state, including HIE-specific things like type index mapping
data TyASTState = TyASTState {
  _tyast_ty_idx_map :: M.Map (T.Text, Int) Int -- path + ty idx -> neo4j idx
  , _tyast_aststate :: ASTState
}
makeLenses ''TyASTState

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

instance Fieldable T.Text where
  mkField = S

field2neo4j_ty :: Field -> T.Text
field2neo4j_ty = \case
  I _ -> ":INT"
  F _ -> ":FLOAT"
  S _ -> ":STRING"

-- thanks https://stackoverflow.com/a/46113439/3925507
modifyingM :: MonadState s m => L.Lens' s a -> (a -> m a) -> m ()
modifyingM l f = do
  old <- L.use l
  new <- f old
  l .= new

-- modifyM :: MonadState s m => (s -> m s) -> m ()
-- modifyM f = do
--   old <- get
--   new <- f old
--   put new

type ASTStateT a = StateT ASTState IO a
type TyASTStateT a = StateT TyASTState IO a

-- magic params are labelled with their keys directly, rather than their types. They're always nameless (subject to change?)
write_entity :: EntityType -> T.Text -> M.Map T.Text Field -> M.Map T.Text Field -> ASTStateT ()
write_entity entity_ty label magic_params params = do
  let all_params = M.keysSet magic_params `S.union` M.keysSet params
      m_new_file = do
        idx <- gets (fromMaybe 0 . fmap (M.size . snd) . (M.!? label) . (^. ast_keys)) -- super sketchy. We need to 
        let fname = "tmp/" ++ filter isAlphaNum (T.unpack label) ++ (show idx) ++ ".csv"
            header =
              M.keys magic_params
              ++ map (uncurry T.append . second field2neo4j_ty) (M.toAscList params)
              -- NOTE this is a different order from `all_params`, which UNIONS the sets together. DO NOT EVER USE IT FOR WRITING HEADERS.
              
        handle <- lift $ openFile fname WriteMode
        -- write header
        lift $ BL.hPut handle $ CSV.encode [header]
        return (handle, T.pack fname)
      row =
        -- S label :
        M.elems magic_params
        ++ M.elems params
  
  -- i'm sure there's a nice way to both set and return the set value using lenses, but i can't be bothered right now, so we'll set blindly then get
  modifyingM ast_keys $ M.alterF (\mv -> Just <$> case mv of
      Just v -> (bisequence . ($ v) . (pure ***)) $ M.alterF (\mv' -> case mv' of
          Just _v' -> pure mv'
          Nothing -> Just <$> m_new_file
        ) all_params
      Nothing -> ((entity_ty, ) . M.singleton all_params) <$> m_new_file
    ) label
  (handle, _) <- ((M.! all_params) . snd . (M.! label)) <$> gets (^. ast_keys)
  void $ lift $ BL.hPut handle $ CSV.encode [row]

write_node :: T.Text -> [(T.Text, Field)] -> ASTStateT Int
write_node label params_raw = do
  idx <- ast_nodeid <<%= (+1) -- postfix ++
  let params = M.fromList params_raw
      magic_params = M.fromList [ ":ID" =: idx ]
  write_entity Neo4JNode label magic_params params
  pure idx

write_rel :: T.Text -> Int -> Int -> [(T.Text, Field)] -> ASTStateT ()
write_rel label from_idx to_idx params_raw = do
  let params = M.fromList params_raw
      magic_params = M.fromList [
          ":START_ID" =: from_idx
          , ":END_ID" =: to_idx
        ]
  write_entity Neo4JRelationship label magic_params params

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

-- is there a nicer, lensical way of doing this?
nest :: Monad m => L.Lens' s a -> StateT a m c -> StateT s m c
nest lout min = do
  sout <- gets (^. lout)
  (c, sout') <- lift $ runStateT min sout
  lout .= sout'
  pure c

ast2cypher :: FilePath -> FilePath -> HieAST TypeIndex -> TyASTStateT Int -- Bolt.BoltActionT IO Int -- IO ()
ast2cypher hs_path hie_path (Node {..}) = do
    let (ann_ctors, ann_tys) = both (map unpackFS) $ unzip $ S.toList $ nodeAnnotations nodeInfo -- S.toList $ S.map (("annotations" =:) . T.pack . UBL.toString . Aeson.encode . both unpackFS)
        -- (sp_fn, sp_l0, sp_ch0, sp_lf, sp_chf) = flat_realsrcspan nodeSpan
        sp_props = span2props "" nodeSpan
        
    tymap <- gets (^. tyast_ty_idx_map)
    let cvt x = fromMaybe (error $ show (hie_path, x, M.size tymap)) . (tymap M.!?) . (T.pack hie_path,) $ x
    ast_idx <- nest tyast_aststate $ write_node "GraphieAST" (
        ("ann_ctors" =: ann_ctors)
        : ("ann_tys" =: ann_tys)
        : sp_props
      )
    
    nest tyast_aststate $ do
      -- type relationships
      mapM (\(pos, ty_idx) ->
          write_rel "GRAPHIE_AST2TY" ast_idx (cvt ty_idx) [
                "pos" =: pos
              ]
        ) (zip ([0..] :: [Int]) $ nodeType nodeInfo)
    
      -- context relationships and misc
      mapM (\(ident, (IdentifierDetails {..})) -> do
          let ident_props = case ident of
                Right name -> ["con" =: T.pack "Name", "uniq" =: uniquable2text name, "name" =: getOccString name]
                Left modname -> ["con" =: T.pack "ModuleName", "uniq" =: uniquable2text modname, "name" =: moduleNameString modname]
          
          ident_idx <- write_node "GraphieIdent" ident_props
          
          write_rel "GRAPHIE_AST2IDENT" ast_idx ident_idx []
          
          _ <- mapM (\ctx -> do
              ctx_idx <- ctxinfo2cypher ctx
              write_rel "GRAPHIE_AST2CTX" ast_idx ctx_idx []
            ) (S.toList identInfo)
          
          case identType of
            Just ty_idx -> do
              void $ write_rel "GRAPHIE_IDENT2TY" ident_idx (cvt ty_idx) []
            Nothing -> pure ()
        ) (M.assocs (nodeIdentifiers nodeInfo))
    
    next_idxs <- mapM (ast2cypher hs_path hie_path) nodeChildren
      
    nest tyast_aststate $ (flip (`zipWithM` ([0..] :: [Int])) next_idxs) $ \pos next_idx -> write_rel "GRAPHIE_AST2AST" ast_idx next_idx ["pos" =: pos]
      
    return ast_idx
    
  where -- TODO refine encapsulations
    mk_ctx_query con props = write_node "GraphieCtx" (
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

getOccString :: Name -> String
getOccString = occNameString . nameOccName

datactor2text :: Data d => d -> Text
datactor2text = T.pack . showConstr . toConstr 

types2cypher :: FilePath -> [(TypeIndex, HieTypeFlat)] -> TyASTStateT () -- Bolt.BoltActionT IO ()
types2cypher path tys = do
  -- insert nodes first
  (M.fromList -> tymap) <- nest tyast_aststate $ mapM (\(idx, ty) -> case ty of
      HTyVarTy name -> mk_ty_query idx "TyVarTy" ["name" =: getOccString name, "uniq" =: uniquable2text name]
      HAppTy _t0 _targs -> mk_ty_query idx "AppTy" []
      HTyConApp (IfaceTyCon { ifaceTyConName }) _targs -> mk_ty_query idx "TyConApp" ["name" =: getOccString ifaceTyConName, "uniq" =: uniquable2text ifaceTyConName]
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
  
  -- might not be necessary to reference tymap' because all the types should be confined to this path (right?)
  tymap' <- tyast_ty_idx_map <%= (M.union tymap)
  let cvt = (tymap' M.!) . (T.pack path,) -- tempting to build this into the mk_* functions and move them into the `do` body...
  
  --  insert relationships last
  -- TODO maybe make a monad/transformer to sort these into the right order
  void $ nest tyast_aststate $ mapM (\(idx, ty) -> case ty of
      HAppTy t0 (HieArgs tn) -> mk_args_query (cvt t0) (map (second cvt) tn)
      HTyConApp _ (HieArgs tn) -> mk_args_query (cvt idx) (map (second cvt) tn) -- (IfaceTyCon { ifaceTyConName = (getOccString -> name) })
      HForAllTy ((name, ty0), argflag) ty1 -> mk_ty_rel (cvt ty0) (cvt ty1) ["name" =: getOccString name, "uniq" =: uniquable2text name, "argflag" =: datactor2text argflag]
      HFunTy tyarg tyret -> do
        mk_ty_rel (cvt idx) (cvt tyarg) ["pos" =: (0 :: Int)]
        mk_ty_rel (cvt idx) (cvt tyret) ["pos" =: (1 :: Int)]
      HQualTy tyctx tyret -> do
        mk_ty_rel (cvt idx) (cvt tyctx) ["pos" =: (0 :: Int)]
        mk_ty_rel (cvt idx) (cvt tyret) ["pos" =: (1 :: Int)]
      HCastTy ty -> mk_ty_rel (cvt idx) (cvt ty) []
      _ -> pure ()
    ) tys
  where -- TODO optimize by reusing labelled nodes (return from these query ctors) -- TODO clean up encapsulations (e.g. closure over `path` is a bit arbitrary and loose)
    mk_ty_query idx con props = write_node "GraphieTy" (
        ("con" =: T.pack con)
        : ("path" =: T.pack path)
        : ("idx" =: idx)
        : props
      )
      <&> ((T.pack path, idx), )
    mk_args_query t0 tn = void $ mapM (\(argpos, (_argvisible, argt)) -> mk_ty_rel t0 argt ["pos" =: argpos]) (zip ([0..] :: [Int]) tn) -- LOSS _argvisible
    -- TODO URGENT path used to be used to discriminate between type vars of differing paths, this needs to be re-introduced as a query against the state. All the IDs need to be remapped... damn this is a pain.
    mk_ty_rel tya_idx tyb_idx relprops = void $ write_rel "GRAPHIE_TY_REL" tya_idx tyb_idx (("path" =: T.pack path) : relprops)
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
    , "hie_module" =: (moduleNameString $ moduleName hie_module)
    , "hie_module_uniq" =: uniquable2text hie_module
  ]

main :: IO ()
main = do
  dflags <- dynFlagsForPrinting
  nc <- makeNc
    
  do
    dhies <- getArgs -- TODO switch to glob-based
    fhies <- fmap concat $ mapM getHieFilesIn $ dhies
    
    ((^. (tyast_aststate . ast_keys)) -> ks) <- (`execStateT` (TyASTState mempty (ASTState 0 mempty))) $ foldrM (\path nc' -> do
        (hie_file_result -> hie, nc'') <- lift $ readHieFile nc' path
        lift $ putStrLn path
      
        -- base file
        hie_file_idx <- nest tyast_aststate $ write_node "GraphieHieFile" (hiefile_props hie)
        -- types
        -- lift $ print $ map fst $ (A.assocs $ hie_types hie)
        types2cypher path (A.assocs $ hie_types hie)
        -- TODO exported names
        -- i.e. exports2cypher (hie_exports hie)
        -- ASTs
        ast_ids <- mapM (\(fs_name, ast) -> ast2cypher (unpackFS fs_name) path ast) (M.assocs $ getAsts $ hie_asts hie)
        
        nest tyast_aststate $ (`mapM` ast_ids) $ \ast_idx -> 
          write_rel "GRAPHIE_FILE2AST" hie_file_idx ast_idx []
        return nc''
      ) nc fhies
    void $ mapM (hClose . fst) $ concatMap (M.elems . snd) $ M.elems $ ks
    putStrLn $ "neo4j-admin import " ++ concat (intersperse " " [
        (case ty of { Neo4JNode -> "--nodes"; Neo4JRelationship -> "--relationships" })
        ++ ":" ++ T.unpack label
        ++ "=" ++ T.unpack fname
        | (label, (ty, m_fs)) <- M.toList ks
        , (_handle, fname) <- M.elems m_fs
      ])
    
    -- putStrLn $ "neo4j-admin import " ++ (concat $ intersperse " " $ map (\(ty, fs) ->
    --     (case ty of { Neo4JRelationship -> "--relationships"; Neo4JNode -> "--nodes" })
    --     ++ ":" ++ (concat $ intersperse ":" $ map fst fs)
    --     ++ "=\"" ++ (concat $ intersperse "," $ map snd fs) ++ "\""
    --       )
    --       $ M.toList $ M.fromListWith (++) $ [
    --         (ty, [(T.unpack label, T.unpack fname)])
    --         | (label, (ty, m_fs)) <- M.toList ks
    --         , (_handle, fname) <- M.elems m_fs
    --       ]
    --   )