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
import com.uni.se.jocl.expressions.Variable;
import com.uni.se.jocl.expressions.VariableExp;
import com.uni.se.jocl.utils.VariableUtils;

public class O2F_DefCVisitor extends OCL2MSFOLVisitor {

	public O2F_DefCVisitor(DataModel dm, Set<Variable> adhocContextualSet, Map<Expression, DefC> defC) {
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
			// First line
			String newDefCName = "TEMP" + String.valueOf(defC.size());
			List<Variable> fVars = VariableUtils.FVars(iteratorExp);
			if (fVars.isEmpty()) {
				String arguments = "Classifier";
				DefC defCElement = new DefC();
				defCElement.setNameDefinition(String.format("%s (%s) Bool", newDefCName, arguments));
				defCElement.setNameApplied(String.format("(%s %s)", newDefCName, "%s"));
				defC.put(iteratorExp, defCElement);
				String var = iteratorExp.getIterator().getName();
				String type = "Classifier";
				String template = Template.Def_c.select_1;
				String firstArgument = app(defCElement.getNameApplied(), fVars, var);
				evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);

				Expression sourceExp = (OclExp) iteratorExp.getSource();
				List<Variable> fVarsSrc = VariableUtils.FVars(sourceExp);
				evalVisitor = new O2F_EvalVisitor(dm, adhocContextualSet, defC);
				sourceExp.accept(evalVisitor);
				this.additionalConstraints.addAll(evalVisitor.additionalConstraints);
				String secondArgument = app(evalVisitor.getFOLFormulae(), fVarsSrc, var);

				Expression bodyExp = iteratorExp.getBody();
				trueVisitor = new O2F_TrueVisitor(dm, adhocContextualSet, defC);
				bodyExp.accept(trueVisitor);
				this.additionalConstraints.addAll(trueVisitor.additionalConstraints);
				String thirdArgument = trueVisitor.getFOLFormulae();

				defCElement
						.setAssertion(String.format(template, var, type, firstArgument, secondArgument, thirdArgument));
			} else {
//				String template = Template.Def_c.select_0;
			}
			break;
		default:
			break;
		}
	}

	@Override
	public void visit(OperationCallExp operationCallExp) {
		// We don't implement concrete detail for abstract objects.
	}

	@Override
	public void visit(LiteralExp literalExp) {
		// We don't implement concrete detail for abstract objects.
	}

	@Override
	public void visit(StringLiteralExp stringLiteralExp) {
		// StringLiteralExp does not have a Def_c definition
	}

	@Override
	public void visit(BooleanLiteralExp booleanLiteralExp) {
		// BooleanLiteralExp does not have a Def_c definition
	}

	@Override
	public void visit(IntegerLiteralExp integerLiteralExp) {
		// IntegerLiteralExp does not have a Def_c definition
	}

	@Override
	public void visit(PropertyCallExp propertyCallExp) {
		// PropertyCallExp does not have a Def_c definition
	}

	@Override
	public void visit(AssociationClassCallExp associationClassCallExp) {
		// TODO: Implement Def_c definition for association-end expressions of case
		// many-to-many
	}

	@Override
	public void visit(VariableExp variableExp) {
		// VariableExp does not have a Def_c definition
	}

}
