{-# OPTIONS --cubical #-}

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

-- free commutative monoids for sets
import Cubical.Structures.Set.CMon.Free
import Cubical.Structures.Set.CMon.SList
import Cubical.Structures.Set.CMon.CList

-- free monoidal groupoids on groupoids
import Cubical.Structures.Gpd.Mon.Free
import Cubical.Structures.Gpd.Mon.List

-- free symmetric monoidal groupoids on groupoids
import Cubical.Structures.Gpd.SMon.Free
import Cubical.Structures.Gpd.SMon.SList

-- an exhaustive list of all modules:
--
import Everything
