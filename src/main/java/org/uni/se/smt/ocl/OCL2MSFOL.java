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

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.uni.dm2schema.dm.DataModel;
import org.uni.se.smt.file.FileManager;
import org.uni.se.smt.logicvalue.LogicValue;

import com.uni.se.jocl.expressions.Expression;
import com.uni.se.jocl.expressions.OclExp;
import com.uni.se.jocl.expressions.Variable;
import com.uni.se.jocl.parser.simple.SimpleParser;
import com.uni.se.jocl.types.Type;

public class OCL2MSFOL {

	private static DataModel dm;
	private static OclExp exp;
	private static LogicValue lvalue;
	private static Set<Variable> adhocContextualSet = new HashSet<>();
	private static Map<Expression, DefC> defC = new HashMap<Expression, DefC>();

	public static void setExpression(String string) {
		SimpleParser simpleParser = new SimpleParser();
		adhocContextualSet.forEach(simpleParser::putAdhocContextualSet);
		Expression exp_ = simpleParser.parse(string, dm);
		if (exp_ instanceof OclExp)
			exp = (OclExp) exp_;
	}

	public static void setExpression(OclExp oclexp) {
		exp = oclexp;
	}

	public static void putAdhocContextualSet(String vName, String vType) {
		Variable v = new Variable(vName, new Type(vType));
		adhocContextualSet.remove(v);
		adhocContextualSet.add(v);
	}

	public static void setDataModel(DataModel dm_) {
		dm = dm_;
	}

	public static void map2msfol(FileManager fm, boolean isInv) throws IOException {
		OCL2MSFOLVisitor visitor;

		defC = new HashMap<Expression, DefC>();

		if (lvalue == LogicValue.INVALID) {
			visitor = new O2F_InvalidVisitor(dm, adhocContextualSet, defC);
		} else if (lvalue == LogicValue.FALSE) {
			visitor = new O2F_FalseVisitor(dm, adhocContextualSet, defC);
		} else if (lvalue == LogicValue.NULL) {
			visitor = new O2F_NullVisitor(dm, adhocContextualSet, defC);
		} else {
			visitor = new O2F_TrueVisitor(dm, adhocContextualSet, defC);
		}
		exp.accept(visitor);
		

		for (DefC d : defC.values()) {
			fm.writeln(String.format("(declare-fun %s)", d.getNameDefinition()));
			fm.assertln(d.getAssertion());
		}
		for (String constraint : visitor.additionalConstraints) {
			fm.assertln(constraint);
		}

		if (isInv) {
			fm.assertln(visitor.getFOLFormulae());
		} else {
			System.out.println(visitor.getFOLFormulae());
		}
	}

	public static void mapContext(FileManager fm) throws IOException {
		for (Variable v : adhocContextualSet) {
			if ("String".equals(v.getType().getReferredType()) || "Integer".equals(v.getType().getReferredType())) {
				fm.writeln(String.format("(declare-const %s %s)", v.getName(), v.getType()));
			} else {
				fm.writeln(String.format("(declare-const %s %s)", v.getName(), "Classifier"));
				fm.writeln(String.format("(assert (%s %s))", v.getType(), v.getName()));
			}
		}
	}
	
	public static List<String> map2msfol(boolean negation) {
		OCL2MSFOLVisitor visitor;

		List<String> formulas = new ArrayList<>();
		for (Variable v : adhocContextualSet) {
			formulas.add(String.format("(declare-const %s %s)", v.getName(), "Classifier"));
			formulas.add(String.format("(assert (%s %s))", v.getType(), v.getName()));
		}

		defC = new HashMap<Expression, DefC>();

		if (lvalue == LogicValue.INVALID) {
			visitor = new O2F_InvalidVisitor(dm, adhocContextualSet, defC);
		} else if (lvalue == LogicValue.FALSE) {
			visitor = new O2F_FalseVisitor(dm, adhocContextualSet, defC);
		} else if (lvalue == LogicValue.NULL) {
			visitor = new O2F_NullVisitor(dm, adhocContextualSet, defC);
		} else {
			visitor = new O2F_TrueVisitor(dm, adhocContextualSet, defC);
		}
		exp.accept(visitor);

		for (DefC d : defC.values()) {
			formulas.add(String.format("(declare-fun %s)", d.getNameDefinition()));
			formulas.add(String.format("(assert %s)", d.getAssertion()));
		}

//		formulas.add(visitor.getFOLFormulae());
		//TODO: Temporary change
		if (negation) {
			formulas.add(String.format("(assert (not %s))", visitor.getFOLFormulae()));
		} else {
			formulas.add(String.format("(assert %s)", visitor.getFOLFormulae()));
		}
		
		return formulas;
	}

	public static LogicValue getLvalue() {
		return lvalue;
	}

	public static void setLvalue(LogicValue lvalue) {
		OCL2MSFOL.lvalue = lvalue;
	}
}
