// Generated by Rex version 1.0 alpha 5

package org.eclipse.photran.internal.core.f95modelparser;

import java.util.ArrayList;

/**
 * An LALR(1) parser
 */
public class Parser
{
    /**
     * The lexical analyzer
     */
    protected ILexer lexer;

    /**
     * This becomes set to true when we finish parsing
     */
    protected boolean doneParsing;

    /**
     * This is set to true if parsing finishes prematurely due to a syntax error
     */
    protected boolean error;

    /**
     * The current state of the parser
     */
    protected int currentState;

    /**
     * The next token in the input stream
     */
    protected Token lookaheadToken;

    /**
     * Although textbook descriptions of LR parsers suggest a stack containing
     * both states and symbols (terminals and nonterminals), we maintain three
     * parallel stacks: one for states, one for symbols, and one for values
     * returned by user code.  This one holds symbols (terminals and nonterminals).
     */
    protected ArrayList symbolStack;

    /**
     * Although textbook descriptions of LR parsers suggest a stack containing
     * both states and symbols (terminals and nonterminals), we maintain three
     * parallel stacks: one for states, one for symbols, and one for values
     * returned by user code.  This one holds states.
     */
    protected ArrayList stateStack;

    /**
     * Although textbook descriptions of LR parsers suggest a stack containing
     * both states and symbols (terminals and nonterminals), we maintain three
     * parallel stacks: one for states, one for symbols, and one for values
     * returned by user code.  This one holds these values.  When a reduction
     * is performed and user code like <code>return $1 + $2</code> is executed, this
     * is where the values of $1 and $2 come from.
     */
    protected ArrayList valueStack;

    /**
     * Provides access to an ErrorRecovery object, which attempts to
     * recover from syntax errors via error productions in the grammar
     */
    protected ErrorRecovery errorRecovery;

    /**
     * The userActions field refers to an instance of the ParserUserActions
     * class, which contains all of the user code
     */
    protected AbstractParserAction userActions;

    /**
     * The entrypoint to the parser.
     */
    public Object parse(ILexer lexicalAnalyzer, AbstractParserAction parseAction) throws Exception
    {
        errorRecovery = new ErrorRecovery(this);
        lexer = lexicalAnalyzer;
        userActions = parseAction;
        parsingTable = new ParsingTable(parseAction);

        // Initialize the parsing stacks
        symbolStack = new ArrayList();
        stateStack = new ArrayList();
        valueStack = new ArrayList();

        // Run any user-specified initialization code
        userActions.initialize();

        // The parser starts in state 0
        currentState = 0;
        stateStack.add(new Integer(currentState));
        readNextToken();
        doneParsing = false;
        error = false;

        // Repeatedly determine the next action based on the current state
        while (!doneParsing)
            parsingTable.processLookaheadFor(this);

        // Run any user-specified deinitialization code
        userActions.deinitialize();

        // Return the value from the last piece of user code
        // executed in a completed parse (the value associated with the
        // start symbol), or null if parsing failed.
        return (error || valueStack.isEmpty()) ? null : (Object)valueStack.get(valueStack.size()-1);
    }

    void readNextToken() throws Exception
    {
        lookaheadToken = lexer.yylex();
    }

    /**
     * Shift the next input symbol and change the parser to the given state.
     */
    void shiftAndGoToState(int state) throws Exception
    {
        symbolStack.add(lookaheadToken.getTerminal());
        stateStack.add(new Integer(state));
        valueStack.add(lookaheadToken);
        currentState = state;
        readNextToken();
    }

    /**
     * Reduce the top symbolsToPop symbols on the stack to the given nonterminal,
     * and change the parser state accordingly.  This overload is called when reducing to an
     * ordinary nonterminal.
     */
    void reduce(Nonterminal nonterminalToReduceTo, int symbolsToPop)
    {
        for (int i = 0; i < symbolsToPop; i++)
        {
            symbolStack.remove(symbolStack.size() - 1);
            stateStack.remove(stateStack.size() - 1);
        }
        currentState = ((Integer)stateStack.get(stateStack.size()-1)).intValue();
        symbolStack.add(nonterminalToReduceTo);
        stateStack.add(new Integer(parsingTable.getGoToFor(nonterminalToReduceTo, this)));
        currentState = ((Integer)stateStack.get(stateStack.size()-1)).intValue();
    }

    /**
     * Reduce the top symbolsToPop symbols on the stack to the given nonterminal,
     * and change the parser state accordingly.  This overload is called when reducing to a
     * nonterminal derived from an EBNF expression: these nonterminals push their own values
     * onto the valueStack, and so the reduce method does not need to.
     */
    void reduce(Nonterminal nonterminalToReduceTo, int symbolsToPop, Object nonterminalValue)
    {
        for (int i = 0; i < symbolsToPop; i++)
        {
            symbolStack.remove(symbolStack.size() - 1);
            stateStack.remove(stateStack.size() - 1);
        }
        currentState = ((Integer)stateStack.get(stateStack.size()-1)).intValue();
        symbolStack.add(nonterminalToReduceTo);
        valueStack.add(nonterminalValue);
        stateStack.add(new Integer(parsingTable.getGoToFor(nonterminalToReduceTo, this)));
        currentState = ((Integer)stateStack.get(stateStack.size()-1)).intValue();
    }

    /**
     * Indicate that parsing is complete
     */
    void accept()
    {
        doneParsing = true;
    }

    /**
     * Stop parsing: A syntax error was found
     */
    void syntaxError() throws Exception
    {
        if (errorRecovery.recover()) return;
        doneParsing = true;
        error = true;

        // Run any user-specified syntax error code
        userActions.syntaxError();
        throw new SyntaxError(lookaheadToken);
    }

    /**
     * Retrieve the parser's current lookahead token
     */
    Token getLookaheadToken() { return lookaheadToken; }

    /**
     * Retrieve the parser's symbol stack
     */
    ArrayList getSymbolStack() { return symbolStack; }

    /**
     * Retrieve the parser's state stack
     */
    ArrayList getStateStack() { return stateStack; }

    /**
     * Retrieve the parser's value stack
     */
    ArrayList getValueStack() { return valueStack; }

    /**
     * Retrieve the object containing all of the user code
     */
    AbstractParserAction getUserActions() { return userActions; }

    /**
     * Stores the parsing table
     */
    protected ParsingTable parsingTable;

    /**
     * Retrieve the parser's current state (an integer)
     */
    int getCurrentState() { return currentState; }
}