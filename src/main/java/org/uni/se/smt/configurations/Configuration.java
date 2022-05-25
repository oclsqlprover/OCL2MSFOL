package org.uni.se.smt.configurations;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

public class Configuration {
	private String dataModel;
	private List<Context> context;
	private List<String> invariant;
	private String ocl;
	private String filename;

	private static final String ENV_DATAMODEL = "DM";
	private static final String ENV_CONTEXT = "CTX";
	private static final String ENV_INVARIANTS = "INV";
	private static final String ENV_OCL = "OCL";
	private static final String ENV_FILENAME = "FILE";

	public String getDataModel() {
		return dataModel;
	}

	public void setDataModel(String dataModel) {
		this.dataModel = dataModel;
	}

	public List<Context> getContext() {
		return context;
	}

	public void setContext(List<Context> context) {
		this.context = context;
	}

	public List<String> getInvariant() {
		return invariant;
	}

	public void setInvariant(List<String> invariant) {
		this.invariant = invariant;
	}

	public String getOcl() {
		return ocl;
	}

	public void setOcl(String ocl) {
		this.ocl = ocl;
	}

	public String getFilename() {
		return filename;
	}

	public void setFilename(String filename) {
		this.filename = filename;
	}

	public Configuration() {
		final Map<String, String> env = System.getenv();

		final String dataModelPath = env.get(ENV_DATAMODEL);
		if (dataModelPath != null) {
			setDataModel(dataModelPath);
		}

		final String context = env.get(ENV_CONTEXT);
		List<Context> vars = new ArrayList<Context>();
		if(context != null && context != "") {
			List<String> sVars = Arrays.asList(context.split(","));
			for (String sVar : sVars) {
				String[] parts = sVar.split(":");
				Context var = new Context(parts[0], parts[1]);
				vars.add(var);
			}
		}
		setContext(vars);
		
		final String invariants = env.get(ENV_INVARIANTS);
		List<String> sInvariants = new ArrayList<String>();
		if(invariants != null && invariants != "") {
			sInvariants.addAll(Arrays.asList(invariants.split(",")));
		}
		setInvariant(sInvariants);
		
		final String ocl = env.get(ENV_OCL);
		if (ocl != null) {
			setOcl(ocl);
		}
		
		final String fileName = env.get(ENV_FILENAME);
		if (fileName != null) {
			setFilename(fileName);
		}
	}

}
