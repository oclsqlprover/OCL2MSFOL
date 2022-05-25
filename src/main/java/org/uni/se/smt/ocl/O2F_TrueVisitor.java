/**************************************************************************
Copyright 2020 ngpbh
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

@author: ngpbh
***************************************************************************/

package org.uni.se.smt.ocl;

import java.util.List;
import java.util.Map;
import java.util.Set;

import org.uni.dm2schema.dm.DataModel;

import com.uni.se.jocl.expressions.AssociationClassCallExp;
import com.uni.se.jocl.expressions.BooleanLiteralExp;
import com.uni.se.jocl.expressions.Expression;
import com.uni.se.jocl.expressions.IntegerLiteralExp;
import com.uni.se.jocl.expressions.IteratorExp;
import com.uni.se.jocl.expressions.IteratorKind;
import com.uni.se.jocl.expressions.LiteralExp;
import com.uni.se.jocl.expressions.OclExp;
import com.uni.se.jocl.expressions.OperationCallExp;
import com.uni.se.jocl.expressions.PropertyCallExp;
import com.uni.se.jocl.expressions.StringLiteralExp;
import com.uni.se.jocl.expressions.TypeExp;
import com.uni.se.jocl.expressions.Variable;
import com.uni.se.jocl.expressions.VariableExp;
import com.uni.se.jocl.utils.VariableUtils;


public class O2F_TrueVisitor extends OCL2MSFOLVisitor {

	public O2F_TrueVisitor(DataModel dm, Set<Variable> adhocContextualSet, Map<Expression, DefC> defC) {
		this.setDataModel(dm);
		this.setAdhocContextualSet(adhocContextualSet);
		this.defC = defC;
	}

	@Override
	public void visit(Expression exp) {
		// We don't implement concrete detail for abstract objects.
	}

	@Override
	public void visit(IteratorExp iteratorExp) {
		switch (IteratorKind.valueOf(iteratorExp.getKind())) {
		case any:
			break;
		case asBag:
			break;
		case asOrderedSet:
			break;
		case asSequence:
			break;
		case asSet:
			break;
		case at:
			break;
		case collect:
			break;
		case count:
			break;
		case excludes:
			break;
		case excludesAll:
			break;
		case excluding:
			break;
		case exists:
			String template = Template.True.exists;

			String var = iteratorExp.getIterator().getName();
			String type = "Classifier";

			OclExp sourceExp = (OclExp) iteratorExp.getSource();
			List<Variable> fVarsSrc = VariableUtils.FVars(sourceExp);
			evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
			sourceExp.accept(evalVisitor);
			this.additionalConstraints.addAll(evalVisitor.additionalConstraints);
			String firstArgument = app(evalVisitor.getFOLFormulae(), fVarsSrc, var);

			Expression bodyExp = iteratorExp.getBody();
			trueVisitor = new O2F_TrueVisitor(dm, adhocContextualSet, defC);
			bodyExp.accept(trueVisitor);
			this.additionalConstraints.addAll(trueVisitor.additionalConstraints);
			String secondArgument = trueVisitor.getFOLFormulae();

			invalVisitor = new O2F_InvalidVisitor(dm, adhocContextualSet, defC);
			sourceExp.accept(invalVisitor);
			this.additionalConstraints.addAll(invalVisitor.additionalConstraints);
			String thirdArgument = invalVisitor.getFOLFormulae();

			this.setFOLFormulae(String.format(template, var, type, firstArgument, secondArgument, thirdArgument));
			break;
		case first:
			break;
		case flatten:
			break;
		case forAll:
			template = Template.True.forAll;

			var = iteratorExp.getIterator().getName();
			type = "Classifier";

			sourceExp = (OclExp) iteratorExp.getSource();
			fVarsSrc = VariableUtils.FVars(sourceExp);
			evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
			sourceExp.accept(evalVisitor);
			this.additionalConstraints.addAll(evalVisitor.additionalConstraints);
			firstArgument = app(evalVisitor.getFOLFormulae(), fVarsSrc, var);

			bodyExp = iteratorExp.getBody();
			trueVisitor = new O2F_TrueVisitor(dm, adhocContextualSet, defC);
			bodyExp.accept(trueVisitor);
			this.additionalConstraints.addAll(trueVisitor.additionalConstraints);
			secondArgument = trueVisitor.getFOLFormulae();

			invalVisitor = new O2F_InvalidVisitor(dm, adhocContextualSet, defC);
			sourceExp.accept(invalVisitor);
			this.additionalConstraints.addAll(invalVisitor.additionalConstraints);
			thirdArgument = invalVisitor.getFOLFormulae();

			invalVisitor = new O2F_InvalidVisitor(dm, adhocContextualSet, defC);
			bodyExp.accept(invalVisitor);
			this.additionalConstraints.addAll(invalVisitor.additionalConstraints);
			String forthArgument = invalVisitor.getFOLFormulae();

			this.setFOLFormulae(
					String.format(template, var, type, firstArgument, secondArgument, thirdArgument, forthArgument));
			break;
		case includes:
			template = Template.True.includes;
			// TODO: Investigate what is the meaning of this?
			// This can be duplicated. Temporary put it as i.
			var = "i";
			type = "Classifier";

			sourceExp = (OclExp) iteratorExp.getSource();
			fVarsSrc = VariableUtils.FVars(sourceExp);
//			fVarsSrc = VariableUtils.getComplement(adhocContextualSet.stream().collect(Collectors.toList()), fVarsSrc);
			evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
			sourceExp.accept(evalVisitor);
			this.additionalConstraints.addAll(evalVisitor.additionalConstraints);
			firstArgument = app(evalVisitor.getFOLFormulae(), fVarsSrc, var);

			bodyExp = iteratorExp.getBody();
			fVarsSrc = VariableUtils.FVars(bodyExp);
			evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
			bodyExp.accept(evalVisitor);
            this.additionalConstraints.addAll(evalVisitor.additionalConstraints);
			String secondArgumentTemplate = "(= %s %s)";
			String secondsecondArgument = app(evalVisitor.getFOLFormulae(), fVarsSrc, null);
			secondArgument = String.format(secondArgumentTemplate, var, secondsecondArgument);

			invalVisitor = new O2F_InvalidVisitor(dm, adhocContextualSet, defC);
			sourceExp.accept(invalVisitor);
			this.additionalConstraints.addAll(invalVisitor.additionalConstraints);
			thirdArgument = invalVisitor.getFOLFormulae();

			invalVisitor = new O2F_InvalidVisitor(dm, adhocContextualSet, defC);
			bodyExp.accept(invalVisitor);
			this.additionalConstraints.addAll(invalVisitor.additionalConstraints);
			forthArgument = invalVisitor.getFOLFormulae();

			this.setFOLFormulae(
					String.format(template, var, type, firstArgument, secondArgument, thirdArgument, forthArgument));
			break;
		case includesAll:
			break;
		case including:
			break;
		case indexOf:
			break;
		case isEmpty:
			template = Template.True.isEmpty;

			Expression exp = iteratorExp.getSource();
			var = "x";
			type = iteratorExp.getSource().getType().getElementType().getReferredType();

			evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
			exp.accept(evalVisitor);
            this.additionalConstraints.addAll(evalVisitor.additionalConstraints);
			List<Variable> fvExp = VariableUtils.FVars(exp);

			firstArgument = app(evalVisitor.getFOLFormulae(), fvExp, var);

			invalVisitor = new O2F_InvalidVisitor(dm, adhocContextualSet, defC);
			exp.accept(invalVisitor);
			this.additionalConstraints.addAll(invalVisitor.additionalConstraints);
			secondArgument = invalVisitor.getFOLFormulae();

			this.setFOLFormulae(String.format(template, var, "Classifier", firstArgument, secondArgument));
			break;
		case isUnique:
			break;
		case last:
			break;
		case notEmpty:
			template = Template.True.notEmpty;

			exp = iteratorExp.getSource();
			var = "x";
			type = iteratorExp.getSource().getType().getElementType().getReferredType();

			evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
			exp.accept(evalVisitor);
            this.additionalConstraints.addAll(evalVisitor.additionalConstraints);
			fvExp = VariableUtils.FVars(exp);

			firstArgument = app(evalVisitor.getFOLFormulae(), fvExp, var);

			invalVisitor = new O2F_InvalidVisitor(dm, adhocContextualSet, defC);
			exp.accept(invalVisitor);
			this.additionalConstraints.addAll(invalVisitor.additionalConstraints);
			secondArgument = invalVisitor.getFOLFormulae();

			this.setFOLFormulae(String.format(template, var, "Classifier", firstArgument, secondArgument));
			break;
		case one:
			break;
		case reject:
			break;
		case select:
			break;
		case size:
			break;
		case sortedBy:
			break;
		case sum:
			break;
		case union:
			break;
		default:
			break;
		}
	}

	@Override
	public void visit(OperationCallExp operationCallExp) {
		switch (operationCallExp.getReferredOperation().getName()) {
		case "allInstances":
			break;
		case "oclIsUndefined":
			String template = Template.True.oclIsUndefined;
			Expression exp = operationCallExp.getSource();
			nullVisitor = new O2F_NullVisitor(dm, adhocContextualSet, defC);
			exp.accept(nullVisitor);
			this.additionalConstraints.addAll(nullVisitor.additionalConstraints);
			invalVisitor = new O2F_InvalidVisitor(dm, adhocContextualSet, defC);
			exp.accept(invalVisitor);
			this.additionalConstraints.addAll(invalVisitor.additionalConstraints);
			this.setFOLFormulae(String.format(template, invalVisitor.getFOLFormulae(), invalVisitor.getFOLFormulae()));
			break;
		case "oclIsInvalid":
			template = Template.True.oclIsInvalid;
			exp = operationCallExp.getSource();
			invalVisitor = new O2F_InvalidVisitor(dm, adhocContextualSet, defC);
			exp.accept(invalVisitor);
			this.additionalConstraints.addAll(invalVisitor.additionalConstraints);
			this.setFOLFormulae(String.format(template, invalVisitor.getFOLFormulae()));
			break;
		case "oclIsKindOf":
			template = Template.True.oclIsKindOf;
			exp = operationCallExp.getSource();
			evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
			exp.accept(evalVisitor);
            this.additionalConstraints.addAll(evalVisitor.additionalConstraints);
			Expression argExp = operationCallExp.getArguments().get(0);
			if (argExp instanceof TypeExp) {
				String typeToCheck;
				typeToCheck = ((TypeExp) argExp).getType().getReferredType();
				this.setFOLFormulae(String.format(template, evalVisitor.getFOLFormulae(), typeOf(typeToCheck)));
			} else {
				String typeToCheck;
				typeToCheck = ((VariableExp) argExp).getType().getReferredType();
				this.setFOLFormulae(String.format(template, evalVisitor.getFOLFormulae(), typeOf(typeToCheck)));
			}
			break;
		case "oclIsTypeOf":
			template = Template.True.oclIsTypeOf;
			exp = operationCallExp.getSource();
			evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
			exp.accept(evalVisitor);
            this.additionalConstraints.addAll(evalVisitor.additionalConstraints);
			argExp = operationCallExp.getArguments().get(0);
			if (argExp instanceof TypeExp) {
				String typeToCheck;
				typeToCheck = ((TypeExp) argExp).getType().getReferredType();
				this.setFOLFormulae(String.format(template, evalVisitor.getFOLFormulae(), typeOf(typeToCheck)));
			} else {
				String typeToCheck;
				typeToCheck = ((VariableExp) argExp).getType().getReferredType();
				this.setFOLFormulae(String.format(template, evalVisitor.getFOLFormulae(), typeOf(typeToCheck)));
			}
			break;
		case "oclAsType":
			break;
		case "=":
			template = Template.True.equality;

			exp = operationCallExp.getSource();
			argExp = operationCallExp.getArguments().get(0);
			nullVisitor = new O2F_NullVisitor(dm, adhocContextualSet, defC);
			exp.accept(nullVisitor);
			this.additionalConstraints.addAll(nullVisitor.additionalConstraints);
			String firstArgument = nullVisitor.getFOLFormulae();
			argExp.accept(nullVisitor);
			this.additionalConstraints.addAll(nullVisitor.additionalConstraints);
			String secondArgument = nullVisitor.getFOLFormulae();
			evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
			exp.accept(evalVisitor);
            this.additionalConstraints.addAll(evalVisitor.additionalConstraints);
			String thirdArgument = evalVisitor.getFOLFormulae();
			argExp.accept(evalVisitor);
            this.additionalConstraints.addAll(evalVisitor.additionalConstraints);
			String forthArgument = evalVisitor.getFOLFormulae();
			invalVisitor = new O2F_InvalidVisitor(dm, adhocContextualSet, defC);
			exp.accept(invalVisitor);
			this.additionalConstraints.addAll(invalVisitor.additionalConstraints);
			String fifthArgument = invalVisitor.getFOLFormulae();
			argExp.accept(invalVisitor);
			this.additionalConstraints.addAll(invalVisitor.additionalConstraints);
			String sixthArgument = invalVisitor.getFOLFormulae();

			this.setFOLFormulae(String.format(template, firstArgument, secondArgument, thirdArgument, forthArgument,
					fifthArgument, sixthArgument));
			break;
		case "<>":
			template = Template.True.inequality;

			exp = operationCallExp.getSource();
			argExp = operationCallExp.getArguments().get(0);
			evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
			exp.accept(evalVisitor);
            this.additionalConstraints.addAll(evalVisitor.additionalConstraints);
			firstArgument = evalVisitor.getFOLFormulae();
			argExp.accept(evalVisitor);
            this.additionalConstraints.addAll(evalVisitor.additionalConstraints);
			secondArgument = evalVisitor.getFOLFormulae();
			nullVisitor = new O2F_NullVisitor(dm, adhocContextualSet, defC);
			exp.accept(nullVisitor);
			this.additionalConstraints.addAll(nullVisitor.additionalConstraints);
			thirdArgument = nullVisitor.getFOLFormulae();
			argExp.accept(nullVisitor);
			this.additionalConstraints.addAll(nullVisitor.additionalConstraints);
			forthArgument = nullVisitor.getFOLFormulae();
			invalVisitor = new O2F_InvalidVisitor(dm, adhocContextualSet, defC);
			exp.accept(invalVisitor);
			this.additionalConstraints.addAll(invalVisitor.additionalConstraints);
			fifthArgument = invalVisitor.getFOLFormulae();
			argExp.accept(invalVisitor);
			this.additionalConstraints.addAll(invalVisitor.additionalConstraints);
			sixthArgument = invalVisitor.getFOLFormulae();

			this.setFOLFormulae(String.format(template, firstArgument, secondArgument, thirdArgument, forthArgument,
					fifthArgument, sixthArgument));
			break;
		case "<=":
		case ">=":
		case ">":
		case "<":
			template = Template.True.lessthan;

			exp = operationCallExp.getSource();
			argExp = operationCallExp.getArguments().get(0);
			nullVisitor = new O2F_NullVisitor(dm, adhocContextualSet, defC);
			exp.accept(nullVisitor);
			this.additionalConstraints.addAll(nullVisitor.additionalConstraints);
			firstArgument = nullVisitor.getFOLFormulae();
			argExp.accept(nullVisitor);
			this.additionalConstraints.addAll(nullVisitor.additionalConstraints);
			secondArgument = nullVisitor.getFOLFormulae();
			evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
			exp.accept(evalVisitor);
            this.additionalConstraints.addAll(evalVisitor.additionalConstraints);
			thirdArgument = evalVisitor.getFOLFormulae();
			argExp.accept(evalVisitor);
            this.additionalConstraints.addAll(evalVisitor.additionalConstraints);
			forthArgument = evalVisitor.getFOLFormulae();
			invalVisitor = new O2F_InvalidVisitor(dm, adhocContextualSet, defC);
			exp.accept(invalVisitor);
			this.additionalConstraints.addAll(invalVisitor.additionalConstraints);
			fifthArgument = invalVisitor.getFOLFormulae();
			argExp.accept(invalVisitor);
			this.additionalConstraints.addAll(invalVisitor.additionalConstraints);
			sixthArgument = invalVisitor.getFOLFormulae();

			this.setFOLFormulae(String.format(template, firstArgument, secondArgument, thirdArgument, forthArgument,
					fifthArgument, sixthArgument));
			break;
		case "and":
			template = Template.True.and;

			exp = operationCallExp.getSource();
			argExp = operationCallExp.getArguments().get(0);

			trueVisitor = new O2F_TrueVisitor(dm, adhocContextualSet, defC);
			exp.accept(trueVisitor);
			this.additionalConstraints.addAll(trueVisitor.additionalConstraints);
			firstArgument = trueVisitor.getFOLFormulae();
			argExp.accept(trueVisitor);
			this.additionalConstraints.addAll(trueVisitor.additionalConstraints);
			secondArgument = trueVisitor.getFOLFormulae();

			this.setFOLFormulae(String.format(template, firstArgument, secondArgument));
			break;
		case "or":
			template = Template.True.or;

			exp = operationCallExp.getSource();
			argExp = operationCallExp.getArguments().get(0);

			trueVisitor = new O2F_TrueVisitor(dm, adhocContextualSet, defC);
			exp.accept(trueVisitor);
			this.additionalConstraints.addAll(trueVisitor.additionalConstraints);
			firstArgument = trueVisitor.getFOLFormulae();
			argExp.accept(trueVisitor);
			this.additionalConstraints.addAll(trueVisitor.additionalConstraints);
			secondArgument = trueVisitor.getFOLFormulae();

			this.setFOLFormulae(String.format(template, firstArgument, secondArgument));
			break;
		case "not":
			template = Template.True.not;
			exp = operationCallExp.getArguments().get(0);
			falseVisitor = new O2F_FalseVisitor(dm, adhocContextualSet, defC);
			exp.accept(falseVisitor);
			this.additionalConstraints.addAll(falseVisitor.additionalConstraints);
			this.setFOLFormulae(String.format(template, falseVisitor.getFOLFormulae()));
			break;
		case "implies":
			template = Template.True.implies;

			exp = operationCallExp.getSource();
			argExp = operationCallExp.getArguments().get(0);

			falseVisitor = new O2F_FalseVisitor(dm, adhocContextualSet, defC);
			exp.accept(falseVisitor);
			this.additionalConstraints.addAll(falseVisitor.additionalConstraints);
			firstArgument = falseVisitor.getFOLFormulae();
			trueVisitor = new O2F_TrueVisitor(dm, adhocContextualSet, defC);
			argExp.accept(trueVisitor);
			this.additionalConstraints.addAll(trueVisitor.additionalConstraints);
			secondArgument = trueVisitor.getFOLFormulae();

			this.setFOLFormulae(String.format(template, firstArgument, secondArgument));
			break;
		case "size":
			break;
		case "isUnique":
			break;
		case "flatten":
			break;
		default:
			break;
		}
	}

	@Override
	public void visit(LiteralExp literalExp) {
		// We don't implement concrete detail for abstract objects.
	}

	@Override
	public void visit(StringLiteralExp stringLiteralExp) {
		// TODO Implement StringLiteralExp for O2Ftrue
	}

	@Override
	public void visit(BooleanLiteralExp booleanLiteralExp) {
		if (booleanLiteralExp.getValue()) {
			this.setFOLFormulae("true");
		} else {
			this.setFOLFormulae("false");
		}
	}

	@Override
	public void visit(IntegerLiteralExp integerLiteralExp) {
		// TODO Implement IntegerLiteralExp for O2Ftrue
	}

	@Override
	public void visit(PropertyCallExp propertyCallExp) {
		// TODO Implement PropertyCallExp for O2Ftrue
	}

	@Override
	public void visit(AssociationClassCallExp associationClassCallExp) {
		// TODO Implement AssociationClassCallExp for O2Ftrue
	}

	@Override
	public void visit(VariableExp variableExp) {
		// TODO Implement VariableExp for O2Ftrue
	}
}
