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

import java.util.Map;
import java.util.Set;

import org.uni.dm2schema.dm.Attribute;
import org.uni.dm2schema.dm.DataModel;
import org.uni.dm2schema.dm.Entity;

import com.uni.se.jocl.expressions.AssociationClassCallExp;
import com.uni.se.jocl.expressions.BooleanLiteralExp;
import com.uni.se.jocl.expressions.Expression;
import com.uni.se.jocl.expressions.IntegerLiteralExp;
import com.uni.se.jocl.expressions.IteratorExp;
import com.uni.se.jocl.expressions.IteratorKind;
import com.uni.se.jocl.expressions.LiteralExp;
import com.uni.se.jocl.expressions.M2OAssociationClassCallExp;
import com.uni.se.jocl.expressions.O2OAssociationClassCallExp;
import com.uni.se.jocl.expressions.OperationCallExp;
import com.uni.se.jocl.expressions.PropertyCallExp;
import com.uni.se.jocl.expressions.StringLiteralExp;
import com.uni.se.jocl.expressions.Variable;
import com.uni.se.jocl.expressions.VariableExp;

public class O2F_EvalVisitor extends OCL2MSFOLVisitor {

	public O2F_EvalVisitor(DataModel dm, Set<Variable> adhocContextualSet, Map<Expression, DefC> defC) {
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
		case collect:
			break;
		case select:
			defCVisitor = new O2F_DefCVisitor(dm, adhocContextualSet, defC);
			iteratorExp.accept(defCVisitor);
			this.additionalConstraints.addAll(defCVisitor.additionalConstraints);
			String defCNameApplied = defC.get(iteratorExp).getNameApplied();
			this.setFOLFormulae(String.format(defCNameApplied, "%s"));
			break;
		default:
			break;
		}
	}

	@Override
	public void visit(OperationCallExp operationCallExp) {
		switch (operationCallExp.getReferredOperation().getName()) {
		case "allInstances":
			String template = Template.Eval.allInstances;
			String clazz = operationCallExp.getSource().getType().getReferredType();
			this.setFOLFormulae(String.format(template, clazz, "%s"));
			break;
		case "oclIsUndefined":
			break;
		case "oclIsKindOf":
			break;
		case "oclIsTypeOf":
			break;
		case "oclAsType":
			break;
		case "=":
		case "<>":
		case "<=":
		case ">=":
		case ">":
		case "<":
		case "and":
		case "or":
			break;
		case "not":
			break;
		case "implies":
			break;
		case "size":
			break;
		case "isEmpty":
			break;
		case "notEmpty":
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
		String template = Template.Eval.stringLiteral;
		String contraintTemplate = Template.Eval.stringLiteralConstraints;
		this.setFOLFormulae(String.format(template, stringLiteralExp.getValue()));
		this.addConstraint(String.format(contraintTemplate, stringLiteralExp.getValue()));
	}

	@Override
	public void visit(BooleanLiteralExp booleanLiteralExp) {
		// TODO Implement BooleanLiteralExp in O2F_eval definition

	}

	@Override
	public void visit(IntegerLiteralExp integerLiteralExp) {
		String template = Template.Eval.intLiteral;
		String contraintTemplate = Template.Eval.intLiteralConstraints;
		this.setFOLFormulae(String.format(template, Integer.toString(integerLiteralExp.getValue())));
		this.addConstraint(String.format(contraintTemplate, Integer.toString(integerLiteralExp.getValue())));
	}

	@Override
	public void visit(PropertyCallExp propertyCallExp) {
		String property = propertyCallExp.getReferredProperty();
		String clazz = null;
		for (Entity e : dm.getEntities().values()) {
			for (Attribute att : e.getAttributes()) {
				if (att.getName().equals(property)) {
					clazz = e.getName();
				}
			}
		}
		evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
		Expression exp = propertyCallExp.getNavigationSource();
		exp.accept(evalVisitor);
		this.additionalConstraints.addAll(evalVisitor.additionalConstraints);
		String template = Template.Eval.attribute;
		this.setFOLFormulae(String.format(template, property, evalVisitor.getFOLFormulae(), clazz));
	}

	@Override
	public void visit(AssociationClassCallExp associationClassCallExp) {
		if (associationClassCallExp instanceof O2OAssociationClassCallExp) {
			String association = associationClassCallExp.getAssociation();
			String clazz = associationClassCallExp.getReferredAssociationEndType().getReferredType();
			evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
			Expression exp = associationClassCallExp.getNavigationSource();
			exp.accept(evalVisitor);
			this.additionalConstraints.addAll(evalVisitor.additionalConstraints);
			String template = Template.Eval.association_0_1_arity;
			this.setFOLFormulae(String.format(template, association, evalVisitor.getFOLFormulae(), clazz));
		} else if (associationClassCallExp instanceof M2OAssociationClassCallExp
				&& ((M2OAssociationClassCallExp) associationClassCallExp).isOneEndAssociationCall()) {
			String association = associationClassCallExp.getAssociation();
			String clazz = associationClassCallExp.getReferredAssociationEndType().getReferredType();
			evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
			Expression exp = associationClassCallExp.getNavigationSource();
			exp.accept(evalVisitor);
			this.additionalConstraints.addAll(evalVisitor.additionalConstraints);
			String template = Template.Eval.association_0_1_arity;
			this.setFOLFormulae(String.format(template, association, evalVisitor.getFOLFormulae(), clazz));
		} else {
			String association = associationClassCallExp.getAssociation();
			String template = Template.Eval.association_n_arity;
			evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
			Expression exp = associationClassCallExp.getNavigationSource();
			exp.accept(evalVisitor);
			this.additionalConstraints.addAll(evalVisitor.additionalConstraints);
			this.setFOLFormulae(String.format(template, association, "%s"));
		}
	}

	@Override
	public void visit(VariableExp variableExp) {
		String template = Template.Eval.variable;
		this.setFOLFormulae(String.format(template, variableExp.getVariable().getName()));
	}
}
