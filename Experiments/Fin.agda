{-# OPTIONS --cubical-compatible --safe #-}

module Experiments.Fin where

open import Cubical.Data.Vec
open import Cubical.Data.Unit

test : Vec Unit 2 -> Unit
test (x ∷ y) = x