package org.eclipse.photran.core;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;

import org.eclipse.photran.internal.core.parser.ASTExecutableProgramNode;
import org.eclipse.photran.internal.core.parser.ParseTreeNode;

public class SourcePrinter
{
    private static final String EOL = System.getProperty("line.separator");
    
    private SourcePrinter() {;}
    
    public static String getSourceCodeFromAST(IFortranAST ast)
    {
        String result = getSourceCodeFromASTNode((ASTExecutableProgramNode)ast);
        
        // When we read in the AST, we use a LineAppendingInputStream so that the
        // user does not have to have a final carriage return in their file.  However,
        // we should chop that off here.
        result = result.substring(0, result.length() - EOL.length());
        
        return result;
    }
    
    public static String getSourceCodeFromASTNode(ParseTreeNode node)
    {
        ByteArrayOutputStream out = new ByteArrayOutputStream(4096);
        node.printOn(new PrintStream(out));
        return out.toString();
    }
}
