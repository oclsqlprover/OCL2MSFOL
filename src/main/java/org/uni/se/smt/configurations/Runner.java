package org.uni.se.smt.configurations;



import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;

import org.json.simple.JSONArray;
import org.json.simple.parser.JSONParser;
import org.json.simple.parser.ParseException;
import org.uni.dm2schema.dm.DataModel;
import org.uni.se.smt.dm.DM2MSFOL;
import org.uni.se.smt.file.FileManager;
import org.uni.se.smt.logicvalue.LogicValue;
import org.uni.se.smt.ocl.OCL2MSFOL;

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

public class Runner {
	public static void main(String[] args) throws FileNotFoundException, IOException, ParseException, Exception {
		Configuration c = new Configuration();

		// A file manager is a singleton in charge of writing the MSFOL theory.
		FileManager fm = FileManager.getInstance();
		// enable safemode will ignore the invalid logic value.
		fm.setSafeMode(false);
		// create a file and ready to write
		fm.open(c.getFilename());
		// init MSFOL theory (some headers, auxiliary definitions)
		fm.init();

		// Get datamodel from file
		DataModel dm = setDataModelFromFile(c.getDataModel());
		// Set the datamodel to the current datamodel of the application
		DM2MSFOL.setDataModel(dm);
		// Print the MSFOL for the datamodel
		DM2MSFOL.map2msfol(fm);

		// Set the current datamodel as the contextual model for the OCL expression
		OCL2MSFOL.setDataModel(dm);
		
		for(Context ctx : c.getContext()) {
			OCL2MSFOL.putAdhocContextualSet(ctx.getVar(), ctx.getType());
		}
		
		OCL2MSFOL.mapContext(fm);
		
		for(String invariant : c.getInvariant()) {
			fm.commentln(invariant);
			OCL2MSFOL.setExpression(invariant);
			OCL2MSFOL.setLvalue(LogicValue.TRUE);
			OCL2MSFOL.map2msfol(fm, true);
		}

		// Set the expression as the source expression to translate
		OCL2MSFOL.setExpression(c.getOcl());
		// Set mode (either TRUE, FALSE, NULL or INVALID)
		OCL2MSFOL.setLvalue(LogicValue.TRUE);
		// Perform the mapping
		OCL2MSFOL.map2msfol(fm, false);

		// Close the FileManager to save the file
		fm.close();
	}

	private static DataModel setDataModelFromFile(String filePath)
			throws FileNotFoundException, IOException, ParseException, Exception {
		File dataModelFile = new File(filePath);
		JSONArray dataModelJSONArray = (JSONArray) new JSONParser().parse(new FileReader(dataModelFile));
		DataModel context = new DataModel(dataModelJSONArray);
		return context;
	}

}
