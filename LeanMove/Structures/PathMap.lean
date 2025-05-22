/-
 Copyright Ilya Sergey

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Batteries.Data.HashMap
import Ssreflect.Lang

/- A data structure for mapping pairs of identifiers to regular expressions -/


namespace Regex

/-- Represents a regular expression with labeled transitions -/
structure Regex (Lbl : Type) where
  labels : List Lbl
  endsInDotStar : Bool

/-- Ord instance for Regex Lbl -/
instance [a : Ord Lbl] : Ord (Regex Lbl) where
    compare x y :=
    let _ : LT Lbl := a.toLT
    let _ : BEq Lbl := a.toBEq
    if List.lex x.labels y.labels then .lt else
    if x.labels == y.labels then compare x.endsInDotStar y.endsInDotStar else .gt


/-- Extension type for incremental regex construction -/
inductive Extension (Lbl : Type) where
  | epsilon : Extension Lbl
  | label : Lbl → Extension Lbl
  | dotStar : Extension Lbl

/-- Extend a regex with an extension -/
def extend {Lbl : Type} (self : Regex Lbl) (ext : Extension Lbl) : Regex Lbl :=
  if self.endsInDotStar then self
  else match ext with
    | Extension.epsilon => self
    | Extension.label lbl => { self with labels := self.labels ++ [lbl] }
    | Extension.dotStar => { self with endsInDotStar := true }


/-- Create an epsilon (empty) regex -/
def epsilon {Lbl : Type} : Regex Lbl := {
  labels := [],
  endsInDotStar := false
}

/-- Create a regex from a single label -/
def label {Lbl : Type} (lbl : Lbl) : Regex Lbl := {
  labels := [lbl],
  endsInDotStar := false
}

/-- Create a dot-star regex (.*) -/
def dotStar {Lbl : Type} : Regex Lbl := {
  labels := [],
  endsInDotStar := true
}

/-- Check if the regex is epsilon (empty) -/
def isEpsilon {Lbl : Type} (self : Regex Lbl) : Bool :=
  self.labels.isEmpty && !self.endsInDotStar

/-- Get the abstract size of the regex -/
def abstractSize {Lbl : Type} (self : Regex Lbl) : Nat :=
  1 + self.labels.length + (if self.endsInDotStar then 1 else 0)

/-- Get the public path representation -/
def pubPath {Lbl : Type} (self : Regex Lbl) : (List Lbl × Bool) :=
  (self.labels, self.endsInDotStar)

end Regex
