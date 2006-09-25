// Generated by Ludwig version 1.0 alpha 6

package org.eclipse.photran.internal.core.parser; import org.eclipse.photran.internal.core.lexer.*;


/**
 * <ComponentAttrSpec> ::= tpointer:T_POINTER  :production194
 * <ComponentAttrSpec> ::= tdimension:T_DIMENSION tlparen:T_LPAREN ComponentArraySpec:<ComponentArraySpec> trparen:T_RPAREN  :production195
 */
public class ASTComponentAttrSpecNode extends ParseTreeNode
{
    public ASTComponentAttrSpecNode(Nonterminal nonterminal, Production production)
    {
        super(nonterminal, production);
    }

    public Token getASTTpointer()
    {
        return this.getChildToken("tpointer");
    }

    public Token getASTTdimension()
    {
        return this.getChildToken("tdimension");
    }

    public Token getASTTlparen()
    {
        return this.getChildToken("tlparen");
    }

    public ASTComponentArraySpecNode getASTComponentArraySpec()
    {
        return (ASTComponentArraySpecNode)this.getChild("ComponentArraySpec");
    }

    public Token getASTTrparen()
    {
        return this.getChildToken("trparen");
    }

    protected void visitThisNodeUsing(ASTVisitor visitor) { visitor.visitASTComponentAttrSpecNode(this); }
}