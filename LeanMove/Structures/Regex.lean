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

import Ssreflect.Lang

namespace Regex

inductive Regex (α : Type) where
  | empty : Regex α
  | ε : Regex α
  | char : α → Regex α
  | dot : Regex α
  | union : Regex α → Regex α → Regex α
  | concat : Regex α → Regex α → Regex α
  | star : Regex α → Regex α
  -- Derivative
  -- TODO: Not sure if this is the right place for this
  | deriv : Regex α → α → Regex α

-- TODO: define interpretation of regexes

-- extend a regular expression with a new sequence of characters
def extend (re: Regex α) (ax: List α) := List.foldl (fun re a => Regex.concat re (Regex.char a)) re ax
-- Infix syntax for extend using ∘
infixl:65 " ∘ " => extend

-- Take a derivative of a regex by a list of characters
def der (re: Regex α) (ax: List α) := List.foldl (fun re a => Regex.deriv re a) re ax

-- Interpretation

def interpret_regex {α} (re: Regex α) : List α → Prop :=
  match re with
  | .empty => fun _ ↦ False
  | .ε => fun ax ↦ ax = []
  | .char a => fun ax ↦ ax = [a]
  | .union re1 re2 => fun ax ↦ interpret_regex re1 ax ∨ interpret_regex re2 ax
  | .concat re1 re2 => fun ax ↦
      ∃ ax1 ax2, ax = ax1 ++ ax2        ∧
                interpret_regex re1 ax1 ∧
                interpret_regex re2 ax2
  | .star re => fun ax ↦
      ∃ n, ∃ inner, interpret_regex re inner ∧
                    ax = (List.replicate n inner |> List.flatten)
  -- TODO: Define the language of derivatives
  | _ => fun _ ↦ False

end Regex
