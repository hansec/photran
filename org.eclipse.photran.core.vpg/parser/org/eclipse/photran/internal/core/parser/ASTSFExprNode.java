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

import org.eclipse.photran.internal.core.parser.ASTListNode;
import org.eclipse.photran.internal.core.parser.ASTNode;
import org.eclipse.photran.internal.core.parser.ASTNodeWithErrorRecoverySymbols;
import org.eclipse.photran.internal.core.parser.IASTListNode;
import org.eclipse.photran.internal.core.parser.IASTNode;
import org.eclipse.photran.internal.core.parser.IASTVisitor;
import org.eclipse.photran.internal.core.lexer.Token;

import org.eclipse.photran.internal.core.lexer.*;                   import org.eclipse.photran.internal.core.analysis.binding.ScopingNode;                   import org.eclipse.photran.internal.core.SyntaxException;                   import java.io.IOException;

@SuppressWarnings("all")
public class ASTSFExprNode extends ASTNode
{
    ASTSFTermNode SFTerm; // in ASTSFExprNode
    ASTSignNode rhs; // in ASTSFExprNode
    ASTSFExprNode lhsExpr; // in ASTSFExprNode
    ASTOperatorNode addOp; // in ASTSFExprNode
    IExpr rhsExpr; // in ASTSFExprNode

    public ASTSFTermNode getSFTerm()
    {
        return this.SFTerm;
    }

    public void setSFTerm(ASTSFTermNode newValue)
    {
        this.SFTerm = newValue;
        if (newValue != null) newValue.setParent(this);
    }


    public ASTSignNode getRhs()
    {
        return this.rhs;
    }

    public void setRhs(ASTSignNode newValue)
    {
        this.rhs = newValue;
        if (newValue != null) newValue.setParent(this);
    }


    public ASTSFExprNode getLhsExpr()
    {
        return this.lhsExpr;
    }

    public void setLhsExpr(ASTSFExprNode newValue)
    {
        this.lhsExpr = newValue;
        if (newValue != null) newValue.setParent(this);
    }


    public ASTOperatorNode getAddOp()
    {
        return this.addOp;
    }

    public void setAddOp(ASTOperatorNode newValue)
    {
        this.addOp = newValue;
        if (newValue != null) newValue.setParent(this);
    }


    public IExpr getRhsExpr()
    {
        return this.rhsExpr;
    }

    public void setRhsExpr(IExpr newValue)
    {
        this.rhsExpr = newValue;
        if (newValue != null) newValue.setParent(this);
    }


    @Override
    public void accept(IASTVisitor visitor)
    {
        visitor.visitASTSFExprNode(this);
        visitor.visitASTNode(this);
    }

    @Override protected int getNumASTFields()
    {
        return 5;
    }

    @Override protected IASTNode getASTField(int index)
    {
        switch (index)
        {
        case 0:  return this.SFTerm;
        case 1:  return this.rhs;
        case 2:  return this.lhsExpr;
        case 3:  return this.addOp;
        case 4:  return this.rhsExpr;
        default: throw new IllegalArgumentException("Invalid index");
        }
    }

    @Override protected void setASTField(int index, IASTNode value)
    {
        switch (index)
        {
        case 0:  this.SFTerm = (ASTSFTermNode)value; if (value != null) value.setParent(this); return;
        case 1:  this.rhs = (ASTSignNode)value; if (value != null) value.setParent(this); return;
        case 2:  this.lhsExpr = (ASTSFExprNode)value; if (value != null) value.setParent(this); return;
        case 3:  this.addOp = (ASTOperatorNode)value; if (value != null) value.setParent(this); return;
        case 4:  this.rhsExpr = (IExpr)value; if (value != null) value.setParent(this); return;
        default: throw new IllegalArgumentException("Invalid index");
        }
    }
}

