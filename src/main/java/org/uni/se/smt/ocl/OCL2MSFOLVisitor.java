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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.uni.dm2schema.dm.DataModel;
import org.uni.dm2schema.dm.Entity;

import com.uni.se.jocl.expressions.Expression;
import com.uni.se.jocl.expressions.Variable;
import com.uni.se.jocl.visit.ParserVisitor;


public abstract class OCL2MSFOLVisitor implements ParserVisitor {
    protected DataModel dm;
    protected Set<Variable> adhocContextualSet = new HashSet<>();
    protected Map<Expression, DefC> defC = new HashMap<Expression, DefC>();
    protected List<String> additionalConstraints = new ArrayList<String>();
    
    protected O2F_NullVisitor nullVisitor;
    protected O2F_TrueVisitor trueVisitor;
    protected O2F_FalseVisitor falseVisitor;
    protected O2F_InvalidVisitor invalVisitor;
    protected O2F_EvalVisitor evalVisitor;
    protected O2F_DefCVisitor defCVisitor;

    public void setDataModel(DataModel dm) {
        this.dm = dm;
    }
    
    public DataModel getDataModel() {
        return this.dm;
    }

    private String fol;

    public String getFOLFormulae() {
        return this.fol;
    }
    
    public void setFOLFormulae(String fol) {
        this.fol = fol;
    }
    
    public void addConstraint(String constraint) {
    	this.additionalConstraints.add(constraint);
    }

    protected String app(String folFormulae, List<Variable> fvExp, String var) {
        String parameter = "";
        for (Variable v : fvExp) {
            parameter = parameter.concat(v.getName()).concat(" ");
        }
        if (var != null) {
        	parameter = parameter.concat(var);
        }
        return String.format(folFormulae, parameter);
    }
    
    protected String nullOf(String type) {
        if(isClassType(type)) {
            return "nullClassifier";
        } else if (type.equals("Integer")) {
            return "nullInt";
        } else if (type.equals("String")) {
            return "nullString";
        }
        return null;
    }
    
    protected boolean isClassType(String type) {
        for(Entity e : dm.getEntities().values()) {
            if(e.getName().equals(type)) {
                return true;
            }
        }
        return false;
    }

    protected String invalidOf(String type) {
        if(isClassType(type)) {
            return "invalidClassifier";
        } else if (type.equals("Integer")) {
            return "invalidInt";
        } else if (type.equals("String")) {
            return "invalidString";
        }
        return null;
    }
    
    protected String typeOf(String type) {
        if(isClassType(type)) {
            return type.substring(0, 1).toUpperCase().concat(type.substring(1)).concat("Type");
        } else if (type.equals("Integer")) {
            return "Int";
        } else if (type.equals("String")) {
            return "String";
        }
        return null;
    }

	public Set<Variable> getAdhocContextualSet() {
		return adhocContextualSet;
	}

	public void setAdhocContextualSet(Set<Variable> adhocContextualSet) {
		this.adhocContextualSet = adhocContextualSet;
	}
}
