// Generated by Ludwig version 1.0 alpha 6

package org.eclipse.photran.internal.core.parser; import org.eclipse.photran.internal.core.lexer.*;


/**
 * <ModuleBlock> ::= ModuleBody:<ModuleBody> EndModuleStmt:<EndModuleStmt>  :production26
 * <ModuleBlock> ::= EndModuleStmt:<EndModuleStmt>  :production27
 */
public class ASTModuleBlockNode extends ParseTreeNode
{
    public ASTModuleBlockNode(Nonterminal nonterminal, Production production)
    {
        super(nonterminal, production);
    }

    public ASTModuleBodyNode getASTModuleBody()
    {
        return (ASTModuleBodyNode)this.getChild("ModuleBody");
    }

    public ASTEndModuleStmtNode getASTEndModuleStmt()
    {
        return (ASTEndModuleStmtNode)this.getChild("EndModuleStmt");
    }

    protected void visitThisNodeUsing(ASTVisitor visitor) { visitor.visitASTModuleBlockNode(this); }
}