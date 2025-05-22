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

import LeanMove.Lang
import LeanMove.Structures.PathMap
import LeanMove.Structures.AssocMap

namespace LeanMove.Checker

open Lang
open Lang.MoveLight
open AssocMap
open Regex

-- Environment mapping sites to their types
abbrev SiteEnv := AssocMap Site MoveType

-- Environment mapping variables to their types
abbrev VarEnv := AssocMap Var MoveType

-- Environment mapping pairs of sites to sets regular expressions
abbrev PathSet := Regex Field → Prop
abbrev PathEnv := Site × Site → PathSet

-- TODO define typing relation



end LeanMove.Checker
