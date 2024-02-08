{-# OPTIONS --cubical --safe --exact-split #-}

module index where

-- an organised list of modules:
--
-- universal algebra
-- algebraic theories and 2-theories
import Cubical.Structures.Sig
import Cubical.Structures.Str
import Cubical.Structures.Eq
import Cubical.Structures.Coh

-- free algebras
import Cubical.Structures.Free

-- free monoids on sets
import Cubical.Structures.Set.Mon.Free
import Cubical.Structures.Set.Mon.List
import Cubical.Structures.Set.Mon.Array

-- free commutative monoids on sets
import Cubical.Structures.Set.CMon.Free
import Cubical.Structures.Set.CMon.SList
import Cubical.Structures.Set.CMon.CList
import Cubical.Structures.Set.CMon.PList
import Cubical.Structures.Set.CMon.QFreeMon
import Cubical.Structures.Set.CMon.Bag

-- free monoidal groupoids on groupoids
import Cubical.Structures.Gpd.Mon.Free
import Cubical.Structures.Gpd.Mon.List

-- free symmetric monoidal groupoids on groupoids
import Cubical.Structures.Gpd.SMon.Free
import Cubical.Structures.Gpd.SMon.SList

-- sorting and order equivalence
import Cubical.Structures.Set.CMon.SList.Sort

-- combinatorics properties
import Cubical.Structures.Set.CMon.SList.Seely

-- useful experiments
import Experiments.Norm

-- an exhaustive list of all modules:
--
import Everything
