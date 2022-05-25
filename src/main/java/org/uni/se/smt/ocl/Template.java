/**************************************************************************
 * Copyright 2022
 * 
 * Licensed under the Apache License, Version 2.0 (the "License"); you may not
 * use this file except in compliance with the License. You may obtain a copy of
 * the License at
 * 
 * http://www.apache.org/licenses/LICENSE-2.0
 * 
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations under
 * the License.
 * 
 * @author: Anonymous Author(s)
 ***************************************************************************/

package org.uni.se.smt.ocl;

public class Template {
	public static class True {
		public static String oclIsUndefined = "(or %s %s)";
		public static String oclIsInvalid = "%s";
		public static String oclIsTypeOf = "(OclIsTypeOf %s %s)";
		public static String oclIsKindOf = "(OclIsKindOf %s %s)";
		public static String equality = "(or (and %1$s %2$s) (and (= %3$s %4$s) (not (or %1$s %5$s %2$s %6$s))))";
		public static String inequality = "(and (not (= %s %s)) (not (or %s %s %s %s)))";
		public static String not = "%s";
		public static String and = "(and %s %s)";
		public static String or = "(or %s %s)";
		public static String lessthan = "(and (< %3$s %4$s) (not (or %1$s %5$s %2$s %6$s)))";
		public static String implies = "(or %s %s)";
		public static String isEmpty = "(forall ((%s %s))(and (not %s) (not %s)))";
		public static String notEmpty = "(exists ((%s %s))(and %s (not %s)))";
		public static String forAll = "(forall ((%s %s))(and (=> %s %s) (not %s)))";
		public static String exists = "(exists ((%s %s))(and (and %s %s) (not %s)))";
		public static String includes = "(exists ((%s %s))(and %s %s (not %s) (not %s)))";
	}

	public static class False {
		public static String oclIsUndefined = "(not (or %s %s))";
		public static String oclIsInvalid = "(not %s)";
		public static String oclIsTypeOf = "(not (OclIsTypeOf %s %s))";
		public static String oclIsKindOf = "(not (OclIsKindOf %s %s))";
		public static String equality = "(and (not (= %s %s)) (not (or %s %s %s %s)))";
		public static String inequality = "(or (and %1$s %2$s) (and (= %3$s %4$s) (and (not (or %1$s %5$s %2$s %6$s)))))";
		public static String not = "%s";
		public static String and = "(or %s %s)";
		public static String or = "(and %s %s)";
		public static String implies = "(and %s %s)";
		public static String isEmpty = "(exists ((%s %s))(and %s (not %s)))";
		public static String notEmpty = "(forall ((%s %s))(and (not %s) (not %s)))";
		public static String forAll = "(exists ((%s %s))(and (and %s %s) (not %s)))";
		public static String exists = "(forall ((%s %s))(and (=> %s %s) (not %s)))";
	}

	public static class Null {
		// Boolean expressions
		public static String oclIsUndefined = "false";
		public static String oclIsInvalid = "false";
		public static String oclIsTypeOf = "false";
		public static String oclIsKindOf = "false";
		public static String equality = "false";
		public static String inequality = "false";
		public static String not = "%s";
		public static String and = "(or (and %1$s %2$s) (and %1$s %3$s) (and %4$s %2$s))";
		public static String or = "(or (and %1$s %2$s) (and %1$s %3$s) (and %4$s %2$s))";
		public static String implies = "(or (and %1$s (or %3$s %2$s %4$s)) (and %2$s (or %5$s %1$s %6$s)))";
		public static String isEmpty = "false";
		public static String notEmpty = "false";
		public static String forAll = "(and (not %1$s) (exists ((%2$s %3$s))(and %4$s %5$s)) (forall ((%2$s %3$s))(=> %4$s (or %6$s %5$s))))";
		public static String exists = "(and (not %s) (exists ((%s %s))(and %s %s)) (forall ((%s %s))(=> %s (or %s %s))))";
		// Non-boolean expressions
		public static String intLiteral = "false";
		public static String variable = "(= %s %s)";
		public static String allInstances = "false";
		public static String attribute = "(= %s %s)";
		public static String association_0_1_arity = "(= %s %s)";
		public static String association_n_arity = "false";
	}

	public static class Invalid {
		// Boolean expressions
		public static String oclIsUndefined = "false";
		public static String oclIsInvalid = "false";
		public static String oclIsTypeOf = "false";
		public static String oclIsKindOf = "false";
		public static String equality = "(or (or %3$s %4$s) (and %1$s (not %2$s)) (and (not %1$s) %2$s))";
		public static String inequality = "(or (or %3$s %4$s) (and %1$s (not %2$s)) (and (not %1$s) %2$s))";
		public static String not = "%s";
		public static String and = "(or (and %1$s (or %3$s %4$s %2$s)) (and %2$s (or %5$s %6$s %1$s)))";
		public static String or = "(or (and %1$s (or %3$s %4$s %2$s)) (and %2$s (or %5$s %6$s %1$s)))";
		public static String implies = "(or %s %s)";
		public static String isEmpty = "%s";
		public static String notEmpty = "%s";
		public static String select = "%s";
		public static String forAll = "(or %s (and (exists ((%s %s))(and %s %s)) (forall ((%s %s))(=> %s (or %s %s %s)))))";
		public static String exists = "(or %s (and (exists ((%s %s))(and %s %s)) (forall ((%s %s))(=> %s (or %s %s %s)))))";
		// Non-boolean expressions
		public static String intLiteral = "false";
		public static String variable = "(= %s %s)";
		public static String allInstances = "false";
		public static String attribute = "(or %s %s)";
		public static String association_0_1_arity = "(or %s %s)";
		public static String association_n_arity = "(or %s %s)";
	}

	public static class Eval {
		public static String intLiteral = "%s";
		public static String intLiteralConstraints = "(and (distinct %1$s nullInt) (distinct %1$s invalidInt))";
		public static String stringLiteral = "%s";
		public static String stringLiteralConstraints = "(and (distinct %1$s nullInt) (distinct %1$s invalidInt))";
		public static String variable = "%s";
		public static String allInstances = "(%s %s)";
		public static String attribute = "(%1$s_%3$s %2$s)";
		public static String association_0_1_arity = "(%1$s_%3$s %2$s)";
		public static String association_n_arity = "(%s %s)";
	}

	public static class Def {
		public static String intLiteral = "";
		public static String variable = "";
		public static String allInstances = "%s";
//        public static String attribute = "";
//        public static String association_0_1_arity = "%s(%s)";
	}

	public static class Def_c {
//        public static String intLiteral = "";
//        public static String variable = "";
//        public static String allInstances = "%s";
//        public static String attribute = "";
//        public static String association_0_1_arity = "%s(%s)";
		public static String select_0 = "(forall ((%s %s)) (forall ((%s %s)) (= (%s) (and %s %s))))";
		public static String select_1 = "(forall ((%s %s)) (= %s (and %s %s)))";
	}

	public static class Def_o {
//      public static String intLiteral = "";
//      public static String variable = "";
//      public static String allInstances = "%s";
//      public static String attribute = "";
//      public static String association_0_1_arity = "%s(%s)";
	}
}
