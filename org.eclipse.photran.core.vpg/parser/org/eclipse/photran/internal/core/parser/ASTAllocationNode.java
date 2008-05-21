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

import java.io.PrintStream;
import java.util.Iterator;

import java.util.List;

import org.eclipse.photran.internal.core.parser.Parser.ASTNode;
import org.eclipse.photran.internal.core.parser.Parser.ASTNodeWithErrorRecoverySymbols;
import org.eclipse.photran.internal.core.parser.Parser.IASTListNode;
import org.eclipse.photran.internal.core.parser.Parser.IASTNode;
import org.eclipse.photran.internal.core.parser.Parser.IASTVisitor;
import org.eclipse.photran.internal.core.lexer.Token;

import org.eclipse.photran.internal.core.lexer.*;                   import org.eclipse.photran.internal.core.analysis.binding.ScopingNode;

public class ASTAllocationNode extends ASTNode
{
    IASTListNode<ASTAllocateObjectNode> allocateObject; // in ASTAllocationNode
    org.eclipse.photran.internal.core.lexer.Token hasAllocatedShape; // in ASTAllocationNode
    IASTListNode<ASTSectionSubscriptNode> sectionSubscriptList; // in ASTAllocationNode
    org.eclipse.photran.internal.core.lexer.Token hiddenTRparen; // in ASTAllocationNode

    public IASTListNode<ASTAllocateObjectNode> getAllocateObject()
    {
        return this.allocateObject;
    }

    public void setAllocateObject(IASTListNode<ASTAllocateObjectNode> newValue)
    {
        this.allocateObject = newValue;
    }


    public boolean hasAllocatedShape()
    {
        return this.hasAllocatedShape != null;
    }

    public void setHasAllocatedShape(org.eclipse.photran.internal.core.lexer.Token newValue)
    {
        this.hasAllocatedShape = newValue;
    }


    public IASTListNode<ASTSectionSubscriptNode> getSectionSubscriptList()
    {
        return this.sectionSubscriptList;
    }

    public void setSectionSubscriptList(IASTListNode<ASTSectionSubscriptNode> newValue)
    {
        this.sectionSubscriptList = newValue;
    }


    public void accept(IASTVisitor visitor)
    {
        visitor.visitASTAllocationNode(this);
        visitor.visitASTNode(this);
    }

    @Override protected int getNumASTFields()
    {
        return 4;
    }

    @Override protected IASTNode getASTField(int index)
    {
        switch (index)
        {
        case 0:  return this.allocateObject;
        case 1:  return this.hasAllocatedShape;
        case 2:  return this.sectionSubscriptList;
        case 3:  return this.hiddenTRparen;
        default: return null;
        }
    }

    @Override protected void setASTField(int index, IASTNode value)
    {
        switch (index)
        {
        case 0:  this.allocateObject = (IASTListNode<ASTAllocateObjectNode>)value;
        case 1:  this.hasAllocatedShape = (org.eclipse.photran.internal.core.lexer.Token)value;
        case 2:  this.sectionSubscriptList = (IASTListNode<ASTSectionSubscriptNode>)value;
        case 3:  this.hiddenTRparen = (org.eclipse.photran.internal.core.lexer.Token)value;
        default: throw new IllegalArgumentException("Invalid index");
        }
    }
}

