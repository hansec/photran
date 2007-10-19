/*******************************************************************************
 * Copyright (c) 2007 University of Illinois at Urbana-Champaign and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     UIUC - Initial API and implementation
 *******************************************************************************/
package org.eclipse.photran.internal.core.parser;

import org.eclipse.photran.internal.core.lexer.*;                   import org.eclipse.photran.internal.core.analysis.binding.ScopingNode;

import org.eclipse.photran.internal.core.parser.Parser.*;
import java.util.List;

public class ASTThenPartNode extends InteriorNode
{
    ASTThenPartNode(Production production, List<CSTNode> childNodes, List<CSTNode> discardedSymbols)
    {
         super(production);
         
         for (Object o : childNodes)
             addChild((CSTNode)o);
         constructionFinished();
    }
        
    @Override public InteriorNode getASTParent()
    {
        InteriorNode actualParent = super.getParent();
        
        // If a node has been pulled up in an ACST, its physical parent in
        // the CST is not its logical parent in the ACST
        if (actualParent != null && actualParent.childIsPulledUp(actualParent.findChild(this)))
            return actualParent.getParent();
        else 
            return actualParent;
    }
    
    @Override protected void visitThisNodeUsing(ASTVisitor visitor)
    {
        visitor.visitASTThenPartNode(this);
    }

    public ASTEndIfStmtNode getEndIfStmt()
    {
        if (treeHasBeenModified()) throw new IllegalStateException("Accessor methods cannot be called on the nodes of a CST after it has been modified");

        if (getProduction() == Production.THEN_PART_657)
            return (ASTEndIfStmtNode)getChild(0);
        else if (getProduction() == Production.THEN_PART_658)
            return (ASTEndIfStmtNode)getChild(1);
        else
            return null;
    }

    public ASTConditionalBodyNode getConditionalBody()
    {
        if (treeHasBeenModified()) throw new IllegalStateException("Accessor methods cannot be called on the nodes of a CST after it has been modified");

        if (getProduction() == Production.THEN_PART_658)
            return (ASTConditionalBodyNode)getChild(0);
        else if (getProduction() == Production.THEN_PART_660)
            return (ASTConditionalBodyNode)getChild(0);
        else if (getProduction() == Production.THEN_PART_662)
            return (ASTConditionalBodyNode)getChild(0);
        else
            return null;
    }

    public ASTElseIfConstructNode getElseIfConstruct()
    {
        if (treeHasBeenModified()) throw new IllegalStateException("Accessor methods cannot be called on the nodes of a CST after it has been modified");

        if (getProduction() == Production.THEN_PART_659)
            return (ASTElseIfConstructNode)getChild(0);
        else if (getProduction() == Production.THEN_PART_660)
            return (ASTElseIfConstructNode)getChild(1);
        else
            return null;
    }

    public ASTElseConstructNode getElseConstruct()
    {
        if (treeHasBeenModified()) throw new IllegalStateException("Accessor methods cannot be called on the nodes of a CST after it has been modified");

        if (getProduction() == Production.THEN_PART_661)
            return (ASTElseConstructNode)getChild(0);
        else if (getProduction() == Production.THEN_PART_662)
            return (ASTElseConstructNode)getChild(1);
        else
            return null;
    }
}
