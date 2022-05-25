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
import com.uni.se.jocl.expressions.M2OAssociationClassCallExp;
import com.uni.se.jocl.expressions.O2OAssociationClassCallExp;
import com.uni.se.jocl.expressions.OclExp;
import com.uni.se.jocl.expressions.OperationCallExp;
import com.uni.se.jocl.expressions.PropertyCallExp;
import com.uni.se.jocl.expressions.StringLiteralExp;
import com.uni.se.jocl.expressions.Variable;
import com.uni.se.jocl.expressions.VariableExp;
import com.uni.se.jocl.utils.VariableUtils;


public class O2F_NullVisitor extends OCL2MSFOLVisitor {

	public O2F_NullVisitor(DataModel dm, Set<Variable> adhocContextualSet, Map<Expression, DefC> defC) {
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
			String template = Template.Null.forAll;

			String var = iteratorExp.getIterator().getName();
			String type = "Classifier";

			OclExp sourceExp = (OclExp) iteratorExp.getSource();
			List<Variable> fVarsSrc = VariableUtils.FVars(sourceExp);
			invalVisitor = new O2F_InvalidVisitor(dm, adhocContextualSet, defC);
			sourceExp.accept(invalVisitor);
			this.additionalConstraints.addAll(invalVisitor.additionalConstraints);
			String firstArgument = invalVisitor.getFOLFormulae();

			evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
			sourceExp.accept(evalVisitor);
			this.additionalConstraints.addAll(evalVisitor.additionalConstraints);
			String secondArgument = app(evalVisitor.getFOLFormulae(), fVarsSrc, var);

			Expression bodyExp = iteratorExp.getBody();
			nullVisitor = new O2F_NullVisitor(dm, adhocContextualSet, defC);
			bodyExp.accept(nullVisitor);
			this.additionalConstraints.addAll(nullVisitor.additionalConstraints);
			String thirdArgument = nullVisitor.getFOLFormulae();

			falseVisitor = new O2F_FalseVisitor(dm, adhocContextualSet, defC);
			sourceExp.accept(falseVisitor);
			this.additionalConstraints.addAll(falseVisitor.additionalConstraints);
			String forthArgument = falseVisitor.getFOLFormulae();

			this.setFOLFormulae(
					String.format(template, firstArgument, var, type, secondArgument, thirdArgument, forthArgument));
			break;
		case first:
			break;
		case flatten:
			break;
		case forAll:
			template = Template.Null.forAll;

			var = iteratorExp.getIterator().getName();
			type = "Classifier";

			sourceExp = (OclExp) iteratorExp.getSource();
			fVarsSrc = VariableUtils.FVars(sourceExp);
			invalVisitor = new O2F_InvalidVisitor(dm, adhocContextualSet, defC);
			sourceExp.accept(invalVisitor);
			this.additionalConstraints.addAll(invalVisitor.additionalConstraints);
			firstArgument = invalVisitor.getFOLFormulae();

			evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
			sourceExp.accept(evalVisitor);
			this.additionalConstraints.addAll(evalVisitor.additionalConstraints);
			secondArgument = app(evalVisitor.getFOLFormulae(), fVarsSrc, var);

			bodyExp = iteratorExp.getBody();
			nullVisitor = new O2F_NullVisitor(dm, adhocContextualSet, defC);
			bodyExp.accept(nullVisitor);
			this.additionalConstraints.addAll(nullVisitor.additionalConstraints);
			thirdArgument = nullVisitor.getFOLFormulae();

			trueVisitor = new O2F_TrueVisitor(dm, adhocContextualSet, defC);
			sourceExp.accept(trueVisitor);
			this.additionalConstraints.addAll(trueVisitor.additionalConstraints);
			forthArgument = trueVisitor.getFOLFormulae();

			this.setFOLFormulae(
					String.format(template, firstArgument, var, type, secondArgument, thirdArgument, forthArgument));
			break;
		case includes:
			break;
		case includesAll:
			break;
		case including:
			break;
		case indexOf:
			break;
		case isEmpty:
			template = Template.Null.isEmpty;
			this.setFOLFormulae(template);
			break;
		case isUnique:
			break;
		case last:
			break;
		case notEmpty:
			template = Template.Null.notEmpty;
			this.setFOLFormulae(template);
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
			String template = Template.Null.allInstances;
			this.setFOLFormulae(template);
			break;
		case "oclIsUndefined":
			template = Template.Null.oclIsUndefined;
			this.setFOLFormulae(template);
			break;
		case "oclIsInvalid":
			template = Template.Null.oclIsInvalid;
			this.setFOLFormulae(template);
			break;
		case "oclIsKindOf":
			template = Template.Null.oclIsKindOf;
			this.setFOLFormulae(template);
			break;
		case "oclIsTypeOf":
			template = Template.Null.oclIsTypeOf;
			this.setFOLFormulae(template);
			break;
		case "oclAsType":
			break;
		case "=":
			template = Template.Null.equality;
			this.setFOLFormulae(template);
			break;
		case "<>":
			template = Template.Null.inequality;
			this.setFOLFormulae(template);
			break;
		case "<=":
		case ">=":
		case ">":
		case "<":
		case "and":
			template = Template.Null.and;

			Expression exp = operationCallExp.getSource();
			Expression argExp = operationCallExp.getArguments().get(0);

			nullVisitor = new O2F_NullVisitor(dm, adhocContextualSet, defC);
			exp.accept(nullVisitor);
			this.additionalConstraints.addAll(nullVisitor.additionalConstraints);
			String firstArgument = nullVisitor.getFOLFormulae();
			argExp.accept(nullVisitor);
			this.additionalConstraints.addAll(nullVisitor.additionalConstraints);
			String secondArgument = nullVisitor.getFOLFormulae();
			trueVisitor = new O2F_TrueVisitor(dm, adhocContextualSet, defC);
			exp.accept(trueVisitor);
			this.additionalConstraints.addAll(trueVisitor.additionalConstraints);
			String thirdArgument = trueVisitor.getFOLFormulae();
			argExp.accept(trueVisitor);
			this.additionalConstraints.addAll(trueVisitor.additionalConstraints);
			String forthArgument = trueVisitor.getFOLFormulae();

			this.setFOLFormulae(String.format(template, firstArgument, secondArgument, thirdArgument, forthArgument));
			break;
		case "or":
			template = Template.Null.or;

			exp = operationCallExp.getSource();
			argExp = operationCallExp.getArguments().get(0);

			nullVisitor = new O2F_NullVisitor(dm, adhocContextualSet, defC);
			exp.accept(nullVisitor);
			this.additionalConstraints.addAll(nullVisitor.additionalConstraints);
			firstArgument = nullVisitor.getFOLFormulae();
			argExp.accept(nullVisitor);
			this.additionalConstraints.addAll(nullVisitor.additionalConstraints);
			secondArgument = nullVisitor.getFOLFormulae();
			falseVisitor = new O2F_FalseVisitor(dm, adhocContextualSet, defC);
			exp.accept(falseVisitor);
			this.additionalConstraints.addAll(falseVisitor.additionalConstraints);
			thirdArgument = falseVisitor.getFOLFormulae();
			argExp.accept(falseVisitor);
			this.additionalConstraints.addAll(falseVisitor.additionalConstraints);
			forthArgument = falseVisitor.getFOLFormulae();

			this.setFOLFormulae(String.format(template, firstArgument, secondArgument, thirdArgument, forthArgument));
			break;
		case "not":
			template = Template.Null.not;
			exp = operationCallExp.getArguments().get(0);
			nullVisitor = new O2F_NullVisitor(dm, adhocContextualSet, defC);
			exp.accept(nullVisitor);
			this.additionalConstraints.addAll(nullVisitor.additionalConstraints);
			this.setFOLFormulae(String.format(template, nullVisitor.getFOLFormulae()));
			break;
		case "implies":
			template = Template.Null.implies;

			exp = operationCallExp.getSource();
			argExp = operationCallExp.getArguments().get(0);
			nullVisitor = new O2F_NullVisitor(dm, adhocContextualSet, defC);
			exp.accept(nullVisitor);
			this.additionalConstraints.addAll(nullVisitor.additionalConstraints);
			firstArgument = nullVisitor.getFOLFormulae();
			argExp.accept(nullVisitor);
			this.additionalConstraints.addAll(nullVisitor.additionalConstraints);
			secondArgument = nullVisitor.getFOLFormulae();
			falseVisitor = new O2F_FalseVisitor(dm, adhocContextualSet, defC);
			exp.accept(falseVisitor);
			this.additionalConstraints.addAll(falseVisitor.additionalConstraints);
			String fifthArgument = falseVisitor.getFOLFormulae();
			argExp.accept(falseVisitor);
			this.additionalConstraints.addAll(falseVisitor.additionalConstraints);
			forthArgument = falseVisitor.getFOLFormulae();
			trueVisitor = new O2F_TrueVisitor(dm, adhocContextualSet, defC);
			exp.accept(trueVisitor);
			this.additionalConstraints.addAll(trueVisitor.additionalConstraints);
			String sixthArgument = trueVisitor.getFOLFormulae();
			argExp.accept(trueVisitor);
			this.additionalConstraints.addAll(trueVisitor.additionalConstraints);
			thirdArgument = trueVisitor.getFOLFormulae();

			this.setFOLFormulae(String.format(template, firstArgument, secondArgument, thirdArgument, forthArgument,
					fifthArgument, sixthArgument));
			break;
		case "size":
			break;
		case "isEmpty":
			template = Template.Null.isEmpty;
			this.setFOLFormulae(template);
			break;
		case "notEmpty":
			template = Template.Null.notEmpty;
			this.setFOLFormulae(template);
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
		// TODO Implement StringLiteralExp for O2Fnull

	}

	@Override
	public void visit(BooleanLiteralExp booleanLiteralExp) {
		this.setFOLFormulae("false");
	}

	@Override
	public void visit(IntegerLiteralExp integerLiteralExp) {
		String template = Template.Null.intLiteral;
		this.setFOLFormulae(template);
	}

	@Override
	public void visit(PropertyCallExp propertyCallExp) {
		String template = Template.Null.attribute;
		evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
		propertyCallExp.accept(evalVisitor);
        this.additionalConstraints.addAll(evalVisitor.additionalConstraints);
		String type = propertyCallExp.getType().getReferredType();
		this.setFOLFormulae(String.format(template, evalVisitor.getFOLFormulae(), nullOf(type)));
	}

	@Override
	public void visit(AssociationClassCallExp associationClassCallExp) {
		if (associationClassCallExp instanceof O2OAssociationClassCallExp) {
			String template = Template.Null.association_0_1_arity;
			evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
			associationClassCallExp.accept(evalVisitor);
            this.additionalConstraints.addAll(evalVisitor.additionalConstraints);
			String type = associationClassCallExp.getReferredAssociationEndType().getReferredType();
			this.setFOLFormulae(String.format(template, evalVisitor.getFOLFormulae(), nullOf(type)));
		} else if (associationClassCallExp instanceof M2OAssociationClassCallExp
				&& ((M2OAssociationClassCallExp) associationClassCallExp).isOneEndAssociationCall()) {
			String template = Template.Null.association_0_1_arity;
			evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
			associationClassCallExp.accept(evalVisitor);
            this.additionalConstraints.addAll(evalVisitor.additionalConstraints);
			String type = associationClassCallExp.getReferredAssociationEndType().getReferredType();
			this.setFOLFormulae(String.format(template, evalVisitor.getFOLFormulae(), nullOf(type)));
		}
	}

	@Override
	public void visit(VariableExp variableExp) {
		String template = Template.Null.variable;
		String var = variableExp.getVariable().getName();
		String type = variableExp.getType().getReferredType();
		this.setFOLFormulae(String.format(template, var, nullOf(type)));
	}
}
