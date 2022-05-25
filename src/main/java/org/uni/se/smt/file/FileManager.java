package org.uni.se.smt.file;
import java.io.FileWriter;
import java.io.IOException;

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

public final class FileManager {
    private static FileWriter fileWriter;
    private static final FileManager INSTANCE = new FileManager();
    private boolean safeMode = true;
    private static String azzert = "(assert %s)";
    private static String comment = "; %s";
    
    private FileManager() {}

    public static FileManager getInstance() {
        return INSTANCE;
    }

    public void close() throws IOException {
        fileWriter.close();
    }
    
    public void open(String fileName) throws IOException {
        fileWriter = new FileWriter(fileName);
    }
    
    public void assertln(String content) throws IOException {
        String newContent = String.format(azzert, content);
        writeln(newContent);
    }
    
    public void commentln(String content) throws IOException {
        String newContent = String.format(comment, content);
        writeln(newContent);
    }
    
    public void writeln(String content) throws IOException {
        fileWriter.write(content);
        fileWriter.write("\n");
    }

    public void init() throws IOException {
        // writeln("(set-logic UFSLIA)");
        writeln("(set-option :produce-models true)");
        writeln("(declare-sort Classifier 0)");
        if(!safeMode) writeln("(declare-sort Type 0)");
        writeln("(declare-const nullClassifier Classifier)");
        if(!safeMode) writeln("(declare-const invalidClassifier Classifier)");
        writeln("(declare-const nullInt Int)");
        if(!safeMode) writeln("(declare-const invalidInt Int)");
        writeln("(declare-const nullString String)");
        if(!safeMode) writeln("(declare-const invalidString String)");
        if(!safeMode) assertln("(distinct nullClassifier invalidClassifier)");
        if(!safeMode) assertln("(distinct nullInt invalidInt)");
        if(!safeMode) assertln("(distinct nullString invalidString)");
    }

    public void checkSat() throws IOException {
        writeln("(check-sat)");
    }

    public boolean isSafeMode() {
        return safeMode;
    }

    public void setSafeMode(boolean safeMode) {
        this.safeMode = safeMode;
    }
}
