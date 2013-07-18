/*******************************************************************************
 * Copyright (c) 2009 University of Illinois at Urbana-Champaign and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     UIUC - Initial API and implementation
 *******************************************************************************/
package org.eclipse.photran.internal.ui.editor_vpg.contentassist;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.TreeSet;
import java.util.regex.Pattern;
import java.util.regex.Matcher;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.ITextViewer;
import org.eclipse.jface.text.contentassist.ContentAssistant;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContentAssistProcessor;
import org.eclipse.jface.text.contentassist.IContentAssistant;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.jface.text.contentassist.IContextInformationValidator;
import org.eclipse.photran.internal.core.lexer.Token;
import org.eclipse.photran.internal.core.analysis.binding.Definition;
import org.eclipse.photran.internal.core.analysis.binding.Definition.Classification;
import org.eclipse.photran.internal.core.analysis.binding.ScopingNode;
import org.eclipse.photran.internal.core.analysis.types.Type;
import org.eclipse.photran.internal.core.analysis.types.DerivedType;
import org.eclipse.photran.internal.core.vpg.AnnotationType;
import org.eclipse.photran.internal.core.vpg.PhotranTokenRef;
import org.eclipse.photran.internal.core.parser.ASTDataComponentDefStmtNode;
import org.eclipse.photran.internal.core.parser.ASTDerivedTypeDefNode;
import org.eclipse.photran.internal.core.parser.ASTDerivedTypeStmtNode;
import org.eclipse.photran.internal.core.parser.ASTProcInterfaceNode;
import org.eclipse.photran.internal.core.parser.ASTSeparatedListNode;
import org.eclipse.photran.internal.core.parser.ASTTypeAttrSpecNode;
import org.eclipse.photran.internal.core.parser.ASTTypeBoundProcedurePartNode;
import org.eclipse.photran.internal.core.parser.IASTListNode;
import org.eclipse.photran.internal.core.parser.IASTNode;
import org.eclipse.photran.internal.core.parser.IDerivedTypeBodyConstruct;
import org.eclipse.photran.internal.core.parser.IInternalSubprogram;
import org.eclipse.photran.internal.core.parser.IProcBindingStmt;
import org.eclipse.photran.internal.core.properties.SearchPathProperties;
import org.eclipse.photran.internal.ui.editor.FortranEditor;
import org.eclipse.photran.internal.ui.editor.FortranTemplateCompletionProcessor;
import org.eclipse.photran.internal.ui.editor.FortranStmtPartitionScanner;
import org.eclipse.photran.internal.ui.editor_vpg.FortranEditorTasks;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;

/**
 * Fortran content assist processor which uses the VPG to determine which identifiers are in scope.
 * 
 * @author Jeff Overbey
 */
public class FortranCompletionProcessor implements IContentAssistProcessor
{
    /** Scope map: scopes.get(n) is the qualified name of the scope at line (n+1) */
    ArrayList<String> scopes = new ArrayList<String>();
    
    /** Maps qualified scope names to lists of definitions declared in that scope */
    HashMap<String, TreeSet<Definition>> defs = new HashMap<String, TreeSet<Definition>>();
    
    private String errorMessage = null;

    //private final Color LIGHT_YELLOW = new Color(null, new RGB(255, 255, 191));
    private final Color LIGHT_YELLOW = new Color(null, new RGB(255, 255, 223));
    //private final Color WHITE = new Color(null, new RGB(255, 255, 255));

    public IContentAssistant setup(FortranEditor editor)
    {
        String contentAssistEnabledProperty = new SearchPathProperties().getProperty(
            editor.getIFile(),
            SearchPathProperties.ENABLE_CONTENT_ASSIST_PROPERTY_NAME);
        if (contentAssistEnabledProperty != null && contentAssistEnabledProperty.equals("true")) //$NON-NLS-1$
        {
            FortranEditorTasks.instance(editor).addASTTask(new FortranCompletionProcessorASTTask(this));
            FortranEditorTasks.instance(editor).addVPGTask(new FortranCompletionProcessorVPGTask(this));
            
            ContentAssistant assistant = new ContentAssistant();
            for (String partitionType : FortranStmtPartitionScanner.PARTITION_TYPES)
                assistant.setContentAssistProcessor(this, partitionType);
            assistant.enableAutoActivation(false); //assistant.setAutoActivationDelay(500);
            assistant.setProposalPopupOrientation(IContentAssistant.CONTEXT_INFO_BELOW);
            assistant.setContextInformationPopupBackground(LIGHT_YELLOW);
            assistant.setProposalSelectorBackground(LIGHT_YELLOW);
            return assistant;
        }
        else return null;
    }

    public synchronized ICompletionProposal[] computeCompletionProposals(ITextViewer viewer, int offset)
    {
        FortranCompletionProposalComputer computer = null;
        List<ICompletionProposal> proposals = new ArrayList<ICompletionProposal>(256);
        
        if (defs != null)
        {
    //        return new ICompletionProposal[]
    //        {
    //            new CompletionProposal("Hello", offset, 0, 5),
    //            new CompletionProposal("Goodbye", offset, 0, 7)
    //        };
            
            try
            {
                errorMessage = null;
                
                IDocument document = viewer.getDocument();
                
                int line = determineLineNumberForOffset(offset, document);
                String scopeName = determineScopeNameForLine(line);
                Iterable<Definition> classDefs = determineDefsForClass(offset,line,document,scopeName);
                
                if (scopeName != null)
                    computer = new FortranCompletionProposalComputer(defs, scopeName, document, offset);

                // Include proposals in this order:
                if (classDefs != null && computer != null) {
                    // If we are adding a class method search for it
                    proposals.addAll(computer.proposalsFromTheseDefs(classDefs));
                } else {    
                
                    // 1. Local variables, functions, etc.
                    if (computer != null) proposals.addAll(computer.proposalsFromDefs());
                
                    // 2. Code templates
                    for (ICompletionProposal proposal : new FortranTemplateCompletionProcessor().computeCompletionProposals(viewer, offset))
                        proposals.add(proposal);

                    // 3. Intrinsic procedures
                    if (computer != null) proposals.addAll(computer.proposalsFromIntrinsics());
                }
            }
            catch (Exception e)
            {
                errorMessage = e.getClass().getName() + " - " + e.getMessage(); //$NON-NLS-1$
            }
        }
        
        return proposals.toArray(new ICompletionProposal[proposals.size()]);
    }
    
    private final List<Definition> getDefsForClass(ScopingNode classScope) throws BadLocationException
    {
        // Get known definitions
        List<Definition> classDefs = classScope.getAllDefinitions();
        // Object is a derived type
        if (classScope instanceof ASTDerivedTypeDefNode ) {
            ASTDerivedTypeDefNode typeNode = (ASTDerivedTypeDefNode) classScope;
            // Look for procedures bound as pointer variables
            IASTListNode<IDerivedTypeBodyConstruct> typeBody =  typeNode.getDerivedTypeBody();
            if (typeBody != null) {
                // Search AST variable definitions
                for (IDerivedTypeBodyConstruct var: typeBody)
                {
                    // Skip standard variable clauses
                    if (var instanceof ASTDataComponentDefStmtNode)
                        continue;
                    Token protoken = var.findFirstToken();
                    Iterable< ? extends IASTNode> children = var.getChildren();
                    for (IASTNode child: children){
                        if (!(child instanceof ASTSeparatedListNode))
                            continue;
                        protoken = child.findFirstToken();
                        if (protoken.isIdentifier())
                            break;
                    }
                    // Create definition object
                    PhotranTokenRef mytoken = protoken.getTokenRef();
                    Definition pro_def = new Definition(protoken.getText(),mytoken,Classification.DERIVED_TYPE_COMPONENT,Type.VOID); 
                    classDefs.add(pro_def);
                }
            }
            // Look for standard type-bound procedures
            ASTTypeBoundProcedurePartNode typePro =  typeNode.getTypeBoundProcedurePart();
            if (typePro != null) {
                IASTListNode<IProcBindingStmt> boundPros = typePro.getProcBindingStmts();
                // Parse AST type-bound procedures
                for (IProcBindingStmt procedure: boundPros)
                {
                    Token protoken = procedure.findFirstToken();
                    Iterable< ? extends IASTNode> children = procedure.getChildren();
                    for (IASTNode child: children){
                        protoken = child.findFirstToken();
                        if (protoken.isIdentifier())
                            break;
                    }
                    // Create definition object
                    PhotranTokenRef mytoken = protoken.getTokenRef();
                    Definition pro_def = new Definition(protoken.getText(),mytoken,Classification.DERIVED_TYPE_COMPONENT,Type.VOID); 
                    classDefs.add(pro_def);
                }
            }
        }
        return classDefs;
    }
    
    private final Iterable<Definition> determineDefsForClass(int offset, int line, IDocument document, String scopeName) throws BadLocationException
    {
        String scopeTemp = scopeName;
        ScopingNode parentScope = null;
        List<Definition> classDefs = null;
        ScopingNode classScope = null;
        // Activate based on class method access
        char prev_char = document.getChar(offset-1);
        if (prev_char != '%')
            return classDefs;
        // Get line to analyze
        int line_offset = document.getLineOffset(line);
        int cur_length = offset-line_offset-1;
        String current_line = document.get(line_offset, cur_length);
        // Compute base variable for current class chain
        String current_variable = null;
        Pattern var_pattern = Pattern.compile("[a-zA-Z0-9_%(,)]*"); //$NON-NLS-1$
        Matcher matched_vars = var_pattern.matcher(current_line);
        while (matched_vars.find()) {
            String var_temp = matched_vars.group();
            if (!var_temp.equals("")) //$NON-NLS-1$
                current_variable = matched_vars.group();
        }
        // Handle arrays usage
        current_variable = current_variable.replaceAll("\\(([^\\)]+)\\)", ""); //$NON-NLS-1$ //$NON-NLS-2$
        // Remove leading characters if setting an array index
        int parenLoc = current_variable.lastIndexOf('(');
        if (parenLoc>=0)
        {
            current_variable = current_variable.substring(parenLoc+1);
        }
        // Handle nested classes
        String[] sub_fields = current_variable.split("%"); //$NON-NLS-1$
        String base_variable = sub_fields[0];
        // Search for base variable in currently available scopes
        String type_name = null;
        Iterable<Definition> proposalsToConsider = null;
        while (true)
        {   
            proposalsToConsider = defs.get(scopeTemp);
            if (proposalsToConsider != null)
            {
                for (Definition def : proposalsToConsider)
                {
                    if (def.getClassification().equals(Classification.MAIN_PROGRAM))
                        continue;
                    String identifier = def.getDeclaredName();
                    if (!identifier.equals(base_variable))
                        continue;
                    // Base variable definition found
                    Type var_type = def.getType();
                    if (var_type instanceof DerivedType ) {
                        String[] tmp1 = var_type.toString().split("\\("); //$NON-NLS-1$
                        String[] tmp2 = tmp1[1].split("\\)"); //$NON-NLS-1$
                        type_name = tmp2[0];
                        break;
                    }
                }
            }
            // Exit if type name was determined
            if (type_name != null)
                break;
            // Step to next outer scope if declaration has not been found
            int colon = scopeTemp.indexOf(':');
            if (colon < 0)
                break;
            else
                scopeTemp = scopeTemp.substring(colon+1);
        }
        // Step up remaining scopes looking for type definition
        outerloop:
            while (true)
            {   
                proposalsToConsider = defs.get(scopeTemp);
                if (proposalsToConsider != null)
                {
                    for (Definition def : proposalsToConsider)
                    {
                        if (def.getClassification().equals(Classification.MAIN_PROGRAM))
                            continue;
                        String identifier = def.getDeclaredName();
                        // Type definition found
                        if (identifier.equals(type_name)) {
                            PhotranTokenRef mytoken = def.getTokenRef();
                            Token mydef = mytoken.getASTNode();
                            parentScope = mydef.getEnclosingScope();
                            classScope = mydef.getLocalScope();
                            // Get known definitions
                            classDefs = classScope.getAllDefinitions();
                            // If class chain wait till top level
                            if (sub_fields.length > 1) {
                                break;
                            } else {
                                break outerloop;
                            }
                        }
                    }
                }
                //
                if (classDefs != null)
                    break;
                // Step to next outer scope if declaration has not been found
                int colon = scopeTemp.indexOf(':');
                if (colon < 0)
                    break;
                else
                    scopeTemp = scopeTemp.substring(colon+1);
            }
        // Step up class chain to current type
        if (sub_fields.length > 1) {
            for (int i = 1; i<sub_fields.length; i=i+1)
            {
                // Find variable in current type
                proposalsToConsider = classDefs;
                if (proposalsToConsider != null)
                {
                    for (Definition def : proposalsToConsider)
                    {
                        if (def.getClassification().equals(Classification.MAIN_PROGRAM))
                            continue;
                        //
                        String identifier = def.getDeclaredName();
                        if (!identifier.equals(sub_fields[i]))
                            continue;
                        // Get type name
                        Type var_type = def.getType();
                        if (var_type instanceof DerivedType ) {
                            String[] tmp1 = var_type.toString().split("\\("); //$NON-NLS-1$
                            String[] tmp2 = tmp1[1].split("\\)"); //$NON-NLS-1$
                            type_name = tmp2[0];
                        }
                    }
                }
                // Find new type in parent scope
                proposalsToConsider = parentScope.getAllDefinitions();
                if (proposalsToConsider != null)
                {
                    for (Definition def : proposalsToConsider)
                    {
                        if (def.getClassification().equals(Classification.MAIN_PROGRAM))
                            continue;
                        //
                        String identifier = def.getDeclaredName();
                        if (!identifier.equals(type_name))
                            continue;
                        //
                        PhotranTokenRef mytoken = def.getTokenRef();
                        Token mydef = mytoken.getASTNode();
                        classScope = mydef.getLocalScope();
                    }
                }
            }
        }
        // If we have located the scope get definitions
        if (classScope != null) {
            // Definitions for this scope
            classDefs = getDefsForClass(classScope);
            // Process inherited elements
            PhotranTokenRef mytoken = null;
            while (true) {
                if (classScope instanceof ASTDerivedTypeDefNode ) {
                    Token parentClass = null;
                    ASTDerivedTypeDefNode typeNode = (ASTDerivedTypeDefNode) classScope;
                    // Look for inheritance node
                    ASTDerivedTypeStmtNode typeDef =  typeNode.getDerivedTypeStmt();
                    IASTListNode<ASTTypeAttrSpecNode> defList = typeDef.getTypeAttrSpecList();
                    if (defList != null) {
                        for (ASTTypeAttrSpecNode currDef: defList) {
                            if (!currDef.isExtends())
                                continue;
                            parentClass = currDef.getParentTypeName();
                            List<PhotranTokenRef> possParents = parentScope.manuallyResolve(parentClass);
                            mytoken = possParents.get(0);
                            parentClass = mytoken.getASTNode();
                        }
                    }
                    // Scan parent class for new methods/variables
                    if (parentClass==null) {
                        break;
                    } else {
                        ScopingNode tempScope = parentClass.getLocalScope();
                        // Get known definitions
                        List<Definition> tempDefs = getDefsForClass(tempScope);
                        for (Definition newDef: tempDefs) {
                            boolean overridden = false;
                            for (Definition currDef: classDefs){
                                String currIden = currDef.getDeclaredName();
                                if (currIden.equals(newDef.getDeclaredName()))
                                    overridden = true;
                            }
                            if (!overridden)
                                classDefs.add(newDef);
                        }
                        // Update scope to move up inheritance ladder
                        classScope = tempScope;
                    }
                }
            }
        }
        return classDefs;
    }

    private int determineLineNumberForOffset(int offset, IDocument document) throws BadLocationException
    {
        int line = document.getLineOfOffset(offset);
        
        /*
         * The mapping between scopes and lines is reconfigured only when
         * the editor is reconciled and a new AST is available.  Therefore,
         * if the user adds a line or two at the bottom of the file and
         * invokes content assist before the editor can be reconciled, the
         * line number may be greater than what the last line of the file
         * was the last time we parsed it.  In this case, reset the line
         * to be the last line of the file.
         */
        if (!scopes.isEmpty() && line >= scopes.size())
            line = scopes.size()-1;
        return line;
    }

    private final String determineScopeNameForLine(int line)
    {
        String scopeName = ""; //$NON-NLS-1$
        if (line < scopes.size())
            scopeName = scopes.get(line);
        if (scopeName == null)
            scopeName = ""; //$NON-NLS-1$
        
        /*
         * Again, the mapping between scopes and lines is reconfigured only
         * when the editor is reconciled and a new AST is available.  If
         * the user invokes content assist and the scope is reported to be
         * the outermost scope (""), it's probably because the user has
         * added lines beyond the end-statement of the previous program
         * unit and the editor hasn't been reconciled yet.  (The outermost
         * scope usually contains just a single module or program, so
         * it is rare that a user would type anything below the
         * first program unit, particularly in the outermost scope).
         * Therefore, populate the list of completion proposals based on
         * the *preceding* scope.
         */
        while (scopeName.equals("") && line > 0) //$NON-NLS-1$
        {
            line--;
            if (line < scopes.size())
                scopeName = scopes.get(line);
        }
        return scopeName;
    }

    public IContextInformation[] computeContextInformation(ITextViewer viewer,
                                                           int offset)
    {
        return null;
    }

    public char[] getCompletionProposalAutoActivationCharacters()
    {
        return null;
    }

    public char[] getContextInformationAutoActivationCharacters()
    {
        return null;
    }

    public IContextInformationValidator getContextInformationValidator()
    {
        return null;
    }

    public String getErrorMessage()
    {
        return errorMessage;
    }
}
