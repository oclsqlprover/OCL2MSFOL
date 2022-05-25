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

package org.uni.se.smt.dm;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.uni.dm2schema.dm.Association;
import org.uni.dm2schema.dm.Attribute;
import org.uni.dm2schema.dm.DataModel;
import org.uni.dm2schema.dm.Entity;
import org.uni.dm2schema.dm.Invariant;
import org.uni.dm2schema.dm.Invariants;
import org.uni.se.smt.file.FileManager;
import org.uni.se.smt.ocl.OCL2MSFOL;

public class DM2MSFOL {

	private static class Template {
		public static String ENTITY = "(declare-fun %s (Classifier) Bool)";
		public static String ENTITY_1 = "(not (%s nullClassifier))";
		public static String ENTITY_1_BIS = "(not (%s invalidClassifier))";
		public static String ATTRIBUTE = "(declare-fun %s_%s (Classifier) %s)";
		public static String ATTRIBUTE_1 = "(= (%s_%s nullClassifier) invalid%s)";
		public static String ATTRIBUTE_1_BIS = "(= (%s_%s invalidClassifier) invalid%s)";
		public static String ATTRIBUTE_2 = "(forall ((x Classifier))\r\n" + "    (=> %s\r\n"
				+ "        (distinct (%s_%s x) invalid%s)))";
		public static String ASSOCIATION = "(declare-fun %s (Classifier Classifier) Bool)";
		public static String ASSOCIATION_1 = "(forall ((x Classifier))\r\n" + "    (forall ((y Classifier)) \r\n"
				+ "        (=> (%s x y) \r\n" + "            (and %s %s))))";
		public static String ENTITY_2 = "(forall ((x Classifier)) \r\n" + "    (=> (%s x) (not %s)))";
		public static String ENTITY_3 = "(declare-const %sType Type)";
		public static String ENTITY_3_BIS = "(distinct %sType %sType)";
		public static String ENTITY_4 = "(forall ((x Classifier))\r\n" + "    (and (=> (%1$s x)\r\n"
				+ "             (OclIsTypeOf x %1$sType))\r\n" + "         (=> (OclIsTypeOf x %1$sType)\r\n"
				+ "             (%1$s x))))";
		public static String ENTITY_5 = "(forall ((x Classifier))\r\n" + "    (and (=> %1$s\r\n"
				+ "             (OclIsKindOf x %2$sType))\r\n" + "         (=> (OclIsKindOf x %2$sType)\r\n"
				+ "             %1$s)))";
		public static String ASSOCIATION_2 = "(declare-fun %s_%s (Classifier) Classifier)";
		public static String ASSOCIATION_3 = "(= (%s_%s nullClassifier) invalidClassifier)";
		public static String ASSOCIATION_3_BIS = "(= (%s_%s invalidClassifier) invalidClassifier)";
		public static String ASSOCIATION_4 = "(forall ((x Classifier))\r\n" + "    (=> (%4$s x)\r\n"
				+ "        (or (= (%1$s_%2$s x) nullClassifier)\r\n" + "            (%3$s (%1$s_%2$s x)))))";
		public static String ASSOCIATION_5 = "(forall ((x Classifier))\r\n" + "    (forall ((y Classifier))\r\n"
				+ "        (=> (and (%1$s x)\r\n" + "                 (%2$s y)\r\n"
				+ "                 (= (%2$s_%3$s y) x))\r\n" + "            (%1$s_%4$s x y))))";
		public static String ASSOCIATION_6 = "(forall ((x Classifier))\r\n" + "    (forall ((y Classifier))\r\n"
				+ "        (=> (%1$s_%2$s x y)\r\n" + "            (= (%3$s_%4$s y) x))))";
	}

	public static DataModel dm;

	public static void setDataModel(DataModel dm_) {
		dm = dm_;
	}
	
	public static List<String> map2msfol(DataModel dm_) {
		setDataModel(dm_);
		List<String> formulas = new ArrayList<String>();
		formulas.addAll(generateEntitiesTheory());
		formulas.addAll(generateAttributesTheory());
		formulas.addAll(generateAssociationEndsTheory());
		formulas.addAll(generateAuxiliaryTheory());
		return formulas;
	}

	private static List<String> generateAuxiliaryTheory() {
		List<String> formulas = new ArrayList<String>();
		for (Entity e : dm.getEntities().values()) {
			List<Entity> exclusion = new ArrayList<Entity>();
			for (Entity e_ : dm.getEntities().values()) {
				if (e_ != e) {
					exclusion.add(e_);
				}
			}
			if (exclusion.isEmpty()) {
				break;
			} else if (exclusion.size() == 1) {
				String s = String.format("(%s x)", exclusion.get(0).getName());
				formulas.add(String.format(Template.ENTITY_2, e.getName(), s));
			} else {
				String s = "";
				for (Entity e_ : exclusion) {
					s = s.concat(String.format(" (%s x)", e_.getName()));
				}
				String s_ = String.format("(or%s)", s);
				formulas.add(String.format(Template.ENTITY_2, e.getName(), s_));
			}
		}
		return formulas;
	}

	private static List<String> generateAssociationEndsTheory() {
		List<String> formulas = new ArrayList<String>();
		for (Association as : dm.getAssociations()) {
			if (as.isManyToMany()) {
				formulas.add(String.format(Template.ASSOCIATION, as.getName()));
				String lhs = String.format("(%s x)", as.getLeftEntityName());
				String rhs = String.format("(%s y)", as.getRightEntityName());
				formulas.add(String.format(Template.ASSOCIATION_1, as.getName(), lhs, rhs));
			} else if (as.isManyToOne()) {
				formulas.add(String.format(Template.ASSOCIATION_2, as.getOneEnd().getCurrentClass(),
						as.getOneEnd().getName()));
				formulas.add(String.format(Template.ASSOCIATION_3, as.getOneEnd().getCurrentClass(),
						as.getOneEnd().getName()));
				formulas.add(String.format(Template.ASSOCIATION_3_BIS, as.getOneEnd().getCurrentClass(),
						as.getOneEnd().getName()));
				formulas.add(String.format(Template.ASSOCIATION_4, as.getOneEnd().getCurrentClass(),
						as.getOneEnd().getName(), as.getOneEnd().getTargetClass(), as.getOneEnd().getCurrentClass()));
				String associationName = String.format("%s_%s", as.getManyEnd().getCurrentClass(),
						as.getManyEnd().getName());
				formulas.add(String.format(Template.ASSOCIATION, associationName));
				formulas.add(String.format(Template.ASSOCIATION_1, associationName, String.format("(%s x)", as.getManyEnd().getCurrentClass()),
						String.format("(%s y)", as.getManyEnd().getTargetClass())));
				formulas.add(String.format(Template.ASSOCIATION_5, as.getManyEnd().getCurrentClass(),
						as.getManyEnd().getTargetClass(), as.getManyEnd().getOpp(), as.getManyEnd().getName()));
				formulas.add(String.format(Template.ASSOCIATION_6, as.getManyEnd().getCurrentClass(),
						as.getManyEnd().getName(), as.getManyEnd().getTargetClass(), as.getManyEnd().getOpp()));
			} else {
				// Implement one-to-one transformation from DM2MSFOL
			}
		}
		return formulas;
	}

	private static List<String> generateAttributesTheory() {
		List<String> formulas = new ArrayList<String>();
		for (Entity e : dm.getEntities().values()) {
			formulas.addAll(generateAttributesEntityTheory(e));
		}
		return formulas;
	}

	private static List<String> generateAttributesEntityTheory(Entity e) {
		List<String> formulas = new ArrayList<String>();
		formulas.add(String.format(Template.ENTITY_1_BIS, e.getName()));
		for (Attribute at : e.getAttributes()) {
			formulas.addAll(generateAttributeEntityTheory(e, at));
		}
		return formulas;
	}

	private static List<String> generateAttributeEntityTheory(Entity e, Attribute at) {
		List<String> formulas = new ArrayList<String>();
		formulas.add(String.format(Template.ATTRIBUTE, at.getName(), e.getName(),
				at.getType().compareTo("String") == 0 ? "String" : "Int"));
		formulas.add(String.format(Template.ATTRIBUTE_1, at.getName(), e.getName(),
				at.getType().compareTo("String") == 0 ? "String" : "Int"));
		formulas.add(String.format(Template.ATTRIBUTE_1_BIS, at.getName(), e.getName(),
				at.getType().compareTo("String") == 0 ? "String" : "Int"));
		formulas.add(String.format(Template.ATTRIBUTE_2, e.getName(), at.getName(),
				e.getName(), at.getType().compareTo("String") == 0 ? "String" : "Int"));
		return formulas;
	}

	private static List<String> generateEntitiesTheory() {
		List<String> formulas = new ArrayList<String>();
		for (Entity entity : dm.getEntities().values()) {
			formulas.addAll(generateEntityTheory(entity));
		}
		return formulas;
	}

	private static List<String> generateEntityTheory(Entity e) {
		List<String> formulas = new ArrayList<String>();
		formulas.add(String.format(Template.ENTITY, e.getName()));
		formulas.add(String.format(Template.ENTITY_1, e.getName()));
		return formulas;
	}

	public static void map2msfol(FileManager fileManager) throws IOException {
		setMode(fileManager);
		generateEntitiesTheory(fileManager);
		generateAttributesTheory(fileManager);
		generateAssociationEndsTheory(fileManager);
		generateAuxiliaryTheory(fileManager);

		OCL2MSFOL.setDataModel(dm);

		generateInvariants(fileManager);
	}

	private static void generateInvariants(FileManager fileManager) throws IOException {
		for (Invariants invs : dm.getInvariants()) {
			for (Invariant inv : invs) {
				String invLabel = inv.getLabel();
				String invOcl = inv.getOcl();
				System.out.println(invLabel);
				System.out.println(invOcl);
				OCL2MSFOL.setExpression(invOcl);
				fileManager.commentln(invLabel);
				OCL2MSFOL.map2msfol(fileManager, true);
			}
		}
	}

	private static void generateAuxiliaryTheory(FileManager fileManager) throws IOException {
		for (Entity e : dm.getEntities().values()) {
			List<Entity> exclusion = new ArrayList<Entity>();
			for (Entity e_ : dm.getEntities().values()) {
				if (e_ != e) {
					exclusion.add(e_);
				}
			}
			if (exclusion.isEmpty()) {
				break;
			} else if (exclusion.size() == 1) {
				String s = String.format("(%s x)", exclusion.get(0).getName());
				fileManager.assertln(String.format(Template.ENTITY_2, e.getName(), s));
			} else {
				String s = "";
				for (Entity e_ : exclusion) {
					s = s.concat(String.format(" (%s x)", e_.getName()));
				}
				String s_ = String.format("(or%s)", s);
				fileManager.assertln(String.format(Template.ENTITY_2, e.getName(), s_));
			}
		}
	}

	private static void generateAssociationEndsTheory(FileManager fileManager) throws IOException {
		for (Association as : dm.getAssociations()) {
			if (as.isManyToMany()) {
				fileManager.writeln(String.format(Template.ASSOCIATION, as.getName()));
				String lhs = fileManager.isSafeMode() ? String.format("(%s x)", as.getLeftEntityName())
						: getGeneralizationFormulae(dm.getEntities().get(as.getLeftEntityName()), "x");
				String rhs = fileManager.isSafeMode() ? String.format("(%s y)", as.getRightEntityName())
						: getGeneralizationFormulae(dm.getEntities().get(as.getRightEntityName()), "y");
				fileManager.assertln(String.format(Template.ASSOCIATION_1, as.getName(), lhs, rhs));
			} else if (as.isManyToOne()) {
				fileManager.writeln(String.format(Template.ASSOCIATION_2, as.getOneEnd().getCurrentClass(),
						as.getOneEnd().getName()));
				fileManager.assertln(String.format(Template.ASSOCIATION_3, as.getOneEnd().getCurrentClass(),
						as.getOneEnd().getName()));
				fileManager.assertln(String.format(Template.ASSOCIATION_3_BIS, as.getOneEnd().getCurrentClass(),
						as.getOneEnd().getName()));
				fileManager.assertln(String.format(Template.ASSOCIATION_4, as.getOneEnd().getCurrentClass(),
						as.getOneEnd().getName(), as.getOneEnd().getTargetClass(), as.getOneEnd().getCurrentClass()));
				String associationName = String.format("%s_%s", as.getManyEnd().getCurrentClass(),
						as.getManyEnd().getName());
				fileManager.writeln(String.format(Template.ASSOCIATION, associationName));
				fileManager.assertln(String.format(Template.ASSOCIATION_1, associationName,
						fileManager.isSafeMode() ? String.format("(%s x)", as.getManyEnd().getCurrentClass())
								: getGeneralizationFormulae(dm.getEntities().get(as.getManyEnd().getCurrentClass()), "x"),
						fileManager.isSafeMode() ? String.format("(%s y)", as.getManyEnd().getTargetClass())
								: getGeneralizationFormulae(dm.getEntities().get(as.getManyEnd().getTargetClass()), "y")));
				fileManager.assertln(String.format(Template.ASSOCIATION_5, as.getManyEnd().getCurrentClass(),
						as.getManyEnd().getTargetClass(), as.getManyEnd().getOpp(), as.getManyEnd().getName()));
				fileManager.assertln(String.format(Template.ASSOCIATION_6, as.getManyEnd().getCurrentClass(),
						as.getManyEnd().getName(), as.getManyEnd().getTargetClass(), as.getManyEnd().getOpp()));
			} else {
				// Implement one-to-one transformation from DM2MSFOL
			}
		}
	}

	private static void generateAttributesTheory(FileManager fileManager) throws IOException {
		for (Entity e : dm.getEntities().values()) {
			generateAttributesEntityTheory(fileManager, e);
		}
	}

	private static void generateAttributesEntityTheory(FileManager fileManager, Entity e) throws IOException {
		if (!fileManager.isSafeMode())
			fileManager.assertln(String.format(Template.ENTITY_1_BIS, e.getName()));
		for (Attribute at : e.getAttributes()) {
			generateAttributeEntityTheory(fileManager, e, at);
		}
		if (!fileManager.isSafeMode()) {
			for (Entity _e : dm.getEntities().values()) {
				if (e != _e) {
					fileManager.assertln(String.format(Template.ENTITY_3_BIS, e.getName(), _e.getName()));
				}
			}
			fileManager.assertln(String.format(Template.ENTITY_4, e.getName()));
			fileManager.assertln(String.format(Template.ENTITY_5, getGeneralizationFormulae(e, ""), e.getName()));
		}
	}

	private static void generateAttributeEntityTheory(FileManager fileManager, Entity e, Attribute at)
			throws IOException {
		fileManager.writeln(String.format(Template.ATTRIBUTE, at.getName(), e.getName(),
				at.getType().compareTo("String") == 0 ? "String" : "Int"));
		if (!fileManager.isSafeMode()) {
			fileManager.assertln(String.format(Template.ATTRIBUTE_1, at.getName(), e.getName(),
					at.getType().compareTo("String") == 0 ? "String" : "Int"));
			fileManager.assertln(String.format(Template.ATTRIBUTE_1_BIS, at.getName(), e.getName(),
					at.getType().compareTo("String") == 0 ? "String" : "Int"));
			fileManager.assertln(String.format(Template.ATTRIBUTE_2, getGeneralizationFormulae(e, ""), at.getName(),
					e.getName(), at.getType().compareTo("String") == 0 ? "String" : "Int"));
		}
	}

	private static void generateEntitiesTheory(FileManager fileManager) throws IOException {
		for (Entity e : dm.getEntities().values()) {
			generateEntityTheory(fileManager, e);
		}
	}

	private static void generateEntityTheory(FileManager fileManager, Entity e) throws IOException {
		fileManager.writeln(String.format(Template.ENTITY, e.getName()));
		fileManager.assertln(String.format(Template.ENTITY_1, e.getName()));
		if (!fileManager.isSafeMode()) {
			fileManager.writeln(String.format(Template.ENTITY_3, e.getName()));
		}
	}

	private static void setMode(FileManager fileManager) throws IOException {
		if (!fileManager.isSafeMode()) {
			fileManager.writeln("(declare-fun OclIsTypeOf (Classifier Type) Bool)");
			fileManager.writeln("(declare-fun OclIsKindOf (Classifier Type) Bool)");
		}
	}

	private static String getGeneralizationFormulae(Entity e, String var) {
		Set<Entity> superClasses = new HashSet<Entity>(getSubClasses(e));
		if (var.isEmpty()) {
			if (superClasses.isEmpty()) {
				return String.format("(%s x)", e.getName());
			} else {
				String s = "(or %s)";
				String firstClass = String.format("(%s x)", e.getName());
				for (Entity e_ : superClasses) {
					firstClass = firstClass.concat(String.format(" (%s x)", e_.getName()));
				}
				return String.format(s, firstClass);
			}
		} else {
			if (superClasses.isEmpty()) {
				return String.format("(%s %s)", e.getName(), var);
			} else {
				String s = "(or %s)";
				String firstClass = String.format("(%s %s)", e.getName(), var);
				for (Entity e_ : superClasses) {
					firstClass = firstClass.concat(String.format(" (%s %s)", e_.getName(), var));
				}
				return String.format(s, firstClass);
			}
		}
	}

	private static List<Entity> getSubClasses(Entity e) {
		List<Entity> results = new ArrayList<Entity>();
		for (Entity _e : dm.getEntities().values()) {
			if (isSuperClass(e, _e)) {
				results.add(_e);
			}
		}
		return results;
	}

	private static boolean isSuperClass(Entity e, Entity _e) {
		if (_e.getName() == e.getName())
			return false;
		if (_e.getSuperClass() == null) {
			return false;
		}
		if (_e.getSuperClass().getName() != e.getName()) {
			return isSuperClass(e, _e.getSuperClass());
		}
		return true;
	}
}
