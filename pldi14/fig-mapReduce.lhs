% To compile this file:
% lhs2TeX mapReduce.lhs > fig-mapReduce.tex && pdflatex fig-mapReduce.tex
\documentclass{standalone}
\usepackage{varwidth}
%include lhs2TeX.fmt
%include lhs2TeX.sty
%options --poly

%format v_1
%format v_2
%format v_3
%format k_1
%format k_2
%format key_1
%format key_2
%format m_1
%format m_2
%format group_a
%format group_b
%format op_b
%format inv_b
%format zero_b
%format v_1Group = "group_1"
%format v_3Group = "group_3"

\newcommand{\Keyword}[1]{\mathrm{#1}}

%format Map = "\Keyword{Map}"
%format Int = "\Keyword{Int}"
%format Bag = "\Keyword{Bag}"
%format bagGroup = "\Keyword{groupOnBags}"
%format foldBag = "\Keyword{fold}" Bag
%format singletonBag = "\Keyword{singleton}" Bag
%format id = "\Keyword{id}"
%format AbelianGroup = "\Keyword{Group}"
%format foldMap = "\Keyword{fold}" Map
%format mapGroup = "\Keyword{groupOnMaps}"
%format singletonMap = "\Keyword{singleton}" Map
%format additiveGroup = additiveGroupOnIntegers

% a hack to put comments at the left column
\def\start{\hspace{-2ex}}

% do not display type class bounds
% assumption: type class bounds end with \Rightarrow
% if assumption changes, the macro must be updated.
\def\constraint#1\Rightarrow{}

\begin{document}\begin{varwidth}{500pt}
\fontsize{8pt}{9pt}\selectfont % sigplan \small
\mathindent=0pt

%if False
\begin{code}
import qualified Data.Map as M
type Bag a           = M.Map a Int
type Map k a         = M.Map k a

{-"\start"-}--Types
data AbelianGroup a = AbelianGroup
  { binaryOperation  :: a -> a -> a
  , inverseFunction  :: a -> a
  , identityElement  :: a }

{-"\start"-}--Bag primitives, implemented in metalanguage

singletonBag :: a -> Bag a
singletonBag element = M.singleton element 1

bagGroup :: {-"\constraint"-}Ord a => AbelianGroup (Bag a)
bagGroup = AbelianGroup union negate empty where
  union   = M.unionWith (+)
  negate  = M.map (\ n -> - n)
  empty   = M.empty

foldBag :: {-"\constraint"-}Ord a => AbelianGroup b -> (a -> b) -> Bag a -> b
foldBag (AbelianGroup binop inv zero) f =
  M.foldWithKey g zero where
  g element count acc =
    let op = binop . (if count >= 0 then id else inv)
    in  (iterate (op (f element)) acc) !! (abs count)

{-"\start"-}--Map primitives, implemented in metalanguage

singletonMap :: {-"\constraint"-}Ord k => k -> a -> Map k a
singletonMap = M.singleton

mapGroup :: {-"\constraint"-}(Ord k, Eq v) => AbelianGroup v -> AbelianGroup (Map k v)
mapGroup (AbelianGroup op inv zero) =  AbelianGroup union negate empty where
  union m_1 m_2  = M.filter (/= zero) (M.unionWith op m_1 m_2)
  negate         = M.map inv
  empty          = M.empty

foldMap :: {-"\constraint"-}(Ord k, Eq b) => AbelianGroup a -> AbelianGroup b ->
  (k -> a -> b) -> Map k a -> b
-- Precondition:
-- For each |key :: k|, the function |f key| is
-- a group homomorphism from |group_a| to |group_b|.
foldMap group_a group_b f =
  let AbelianGroup op_b inv_b zero_b = group_b
  in M.foldWithKey (\ key val acc -> op_b (f key val) acc) zero_b
\end{code}
%endif

\begin{code}
histogram :: {-"\constraint"-}(Ord word) => Map Int (Bag word) -> Map word Int
histogram = mapReduce bagGroup additiveGroup histogramMap histogramReduce
  where  additiveGroup      = AbelianGroup (+) (\ n -> - n) 0
         histogramMap _     = foldBag bagGroup (\ n -> singletonBag (n, 1))
         histogramReduce _  = foldBag additiveGroup id

{-"\start"-}-- Precondition:
{-"\start"-}-- For every |key_1 :: k_1| and |key_2 :: k_2|, the terms |mapper key_1| and |reducer key_2| are homomorphisms.
mapReduce ::  {-"\constraint"-}(Ord k_1, Ord k_2, Ord v_1, Ord v_2, Eq v_3) => AbelianGroup v_1 -> AbelianGroup v_3 -> (k_1 -> v_1 -> Bag (k_2, v_2)) -> (k_2 -> Bag v_2 -> v_3) ->
              Map k_1 v_1 -> Map k_2 v_3
mapReduce v_1Group v_3Group mapper reducer = reducePerKey . groupByKey . mapPerKey
  where  mapPerKey     = foldMap  v_1Group bagGroup             mapper
         groupByKey    = foldBag  (mapGroup bagGroup)
                                  (\ (key, val)  -> singletonMap key (singletonBag val))
         reducePerKey  = foldMap  bagGroup (mapGroup v_3Group)
                                  (\ key bag     -> singletonMap key (reducer key bag))
\end{code}
\end{varwidth}\end{document}
