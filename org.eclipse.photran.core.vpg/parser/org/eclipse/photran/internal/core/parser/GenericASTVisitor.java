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

import org.eclipse.photran.internal.core.lexer.*;                   import org.eclipse.photran.internal.core.analysis.binding.ScopingNode;                   import org.eclipse.photran.internal.core.SyntaxException;                   import java.io.IOException;

@SuppressWarnings("all")
public class GenericASTVisitor implements IASTVisitor
{
    protected void traverseChildren(IASTNode node)
    {
        for (IASTNode child : node.getChildren())
            child.accept(this);
    }

    public void visitASTNode(IASTNode node) { traverseChildren(node); }
    public void visitToken(Token node) {}
    public void visitASTListNode(IASTListNode<?> node) {}
    public void visitASTAcImpliedDoNode(ASTAcImpliedDoNode node) {}
    public void visitASTAcValueNode(ASTAcValueNode node) {}
    public void visitASTAccessSpecNode(ASTAccessSpecNode node) {}
    public void visitASTAccessStmtNode(ASTAccessStmtNode node) {}
    public void visitASTAllStopStmtNode(ASTAllStopStmtNode node) {}
    public void visitASTAllocatableStmtNode(ASTAllocatableStmtNode node) {}
    public void visitASTAllocateCoarraySpecNode(ASTAllocateCoarraySpecNode node) {}
    public void visitASTAllocateObjectNode(ASTAllocateObjectNode node) {}
    public void visitASTAllocateStmtNode(ASTAllocateStmtNode node) {}
    public void visitASTAllocatedShapeNode(ASTAllocatedShapeNode node) {}
    public void visitASTAllocationNode(ASTAllocationNode node) {}
    public void visitASTArithmeticIfStmtNode(ASTArithmeticIfStmtNode node) {}
    public void visitASTArrayAllocationNode(ASTArrayAllocationNode node) {}
    public void visitASTArrayConstructorNode(ASTArrayConstructorNode node) {}
    public void visitASTArrayDeclaratorNode(ASTArrayDeclaratorNode node) {}
    public void visitASTArrayElementNode(ASTArrayElementNode node) {}
    public void visitASTArrayNameNode(ASTArrayNameNode node) {}
    public void visitASTArraySpecNode(ASTArraySpecNode node) {}
    public void visitASTAssignStmtNode(ASTAssignStmtNode node) {}
    public void visitASTAssignedGotoStmtNode(ASTAssignedGotoStmtNode node) {}
    public void visitASTAssignmentStmtNode(ASTAssignmentStmtNode node) {}
    public void visitASTAssociateConstructNode(ASTAssociateConstructNode node) {}
    public void visitASTAssociateStmtNode(ASTAssociateStmtNode node) {}
    public void visitASTAssociationNode(ASTAssociationNode node) {}
    public void visitASTAssumedShapeSpecListNode(ASTAssumedShapeSpecListNode node) {}
    public void visitASTAssumedShapeSpecNode(ASTAssumedShapeSpecNode node) {}
    public void visitASTAssumedSizeSpecNode(ASTAssumedSizeSpecNode node) {}
    public void visitASTAsynchronousStmtNode(ASTAsynchronousStmtNode node) {}
    public void visitASTAttrSpecNode(ASTAttrSpecNode node) {}
    public void visitASTAttrSpecSeqNode(ASTAttrSpecSeqNode node) {}
    public void visitASTBackspaceStmtNode(ASTBackspaceStmtNode node) {}
    public void visitASTBinaryExprNode(ASTBinaryExprNode node) {}
    public void visitASTBindStmtNode(ASTBindStmtNode node) {}
    public void visitASTBindingAttrNode(ASTBindingAttrNode node) {}
    public void visitASTBindingPrivateStmtNode(ASTBindingPrivateStmtNode node) {}
    public void visitASTBlockConstructNode(ASTBlockConstructNode node) {}
    public void visitASTBlockDataNameNode(ASTBlockDataNameNode node) {}
    public void visitASTBlockDataStmtNode(ASTBlockDataStmtNode node) {}
    public void visitASTBlockDataSubprogramNode(ASTBlockDataSubprogramNode node) {}
    public void visitASTBlockDoConstructNode(ASTBlockDoConstructNode node) {}
    public void visitASTBlockStmtNode(ASTBlockStmtNode node) {}
    public void visitASTBodyPlusInternalsNode(ASTBodyPlusInternalsNode node) {}
    public void visitASTBozLiteralConstNode(ASTBozLiteralConstNode node) {}
    public void visitASTCExprNode(ASTCExprNode node) {}
    public void visitASTCOperandNode(ASTCOperandNode node) {}
    public void visitASTCPrimaryNode(ASTCPrimaryNode node) {}
    public void visitASTCallStmtNode(ASTCallStmtNode node) {}
    public void visitASTCaseConstructNode(ASTCaseConstructNode node) {}
    public void visitASTCaseSelectorNode(ASTCaseSelectorNode node) {}
    public void visitASTCaseStmtNode(ASTCaseStmtNode node) {}
    public void visitASTCaseValueRangeNode(ASTCaseValueRangeNode node) {}
    public void visitASTCharLenParamValueNode(ASTCharLenParamValueNode node) {}
    public void visitASTCharLengthNode(ASTCharLengthNode node) {}
    public void visitASTCharSelectorNode(ASTCharSelectorNode node) {}
    public void visitASTCloseSpecListNode(ASTCloseSpecListNode node) {}
    public void visitASTCloseSpecNode(ASTCloseSpecNode node) {}
    public void visitASTCloseStmtNode(ASTCloseStmtNode node) {}
    public void visitASTCoarraySpecNode(ASTCoarraySpecNode node) {}
    public void visitASTCodimensionDeclNode(ASTCodimensionDeclNode node) {}
    public void visitASTCodimensionStmtNode(ASTCodimensionStmtNode node) {}
    public void visitASTCommaExpNode(ASTCommaExpNode node) {}
    public void visitASTCommaLoopControlNode(ASTCommaLoopControlNode node) {}
    public void visitASTCommonBlockBinding(ASTCommonBlockBinding node) {}
    public void visitASTCommonBlockNameNode(ASTCommonBlockNameNode node) {}
    public void visitASTCommonBlockNode(ASTCommonBlockNode node) {}
    public void visitASTCommonBlockObjectNode(ASTCommonBlockObjectNode node) {}
    public void visitASTCommonStmtNode(ASTCommonStmtNode node) {}
    public void visitASTComplexConstNode(ASTComplexConstNode node) {}
    public void visitASTComponentArraySpecNode(ASTComponentArraySpecNode node) {}
    public void visitASTComponentAttrSpecNode(ASTComponentAttrSpecNode node) {}
    public void visitASTComponentDeclNode(ASTComponentDeclNode node) {}
    public void visitASTComponentInitializationNode(ASTComponentInitializationNode node) {}
    public void visitASTComponentNameNode(ASTComponentNameNode node) {}
    public void visitASTComputedGotoStmtNode(ASTComputedGotoStmtNode node) {}
    public void visitASTConnectSpecListNode(ASTConnectSpecListNode node) {}
    public void visitASTConnectSpecNode(ASTConnectSpecNode node) {}
    public void visitASTConstantNode(ASTConstantNode node) {}
    public void visitASTContainsStmtNode(ASTContainsStmtNode node) {}
    public void visitASTContiguousStmtNode(ASTContiguousStmtNode node) {}
    public void visitASTContinueStmtNode(ASTContinueStmtNode node) {}
    public void visitASTCrayPointerStmtNode(ASTCrayPointerStmtNode node) {}
    public void visitASTCrayPointerStmtObjectNode(ASTCrayPointerStmtObjectNode node) {}
    public void visitASTCriticalConstructNode(ASTCriticalConstructNode node) {}
    public void visitASTCriticalStmtNode(ASTCriticalStmtNode node) {}
    public void visitASTCycleStmtNode(ASTCycleStmtNode node) {}
    public void visitASTDataComponentDefStmtNode(ASTDataComponentDefStmtNode node) {}
    public void visitASTDataImpliedDoNode(ASTDataImpliedDoNode node) {}
    public void visitASTDataRefNode(ASTDataRefNode node) {}
    public void visitASTDataStmtConstantNode(ASTDataStmtConstantNode node) {}
    public void visitASTDataStmtNode(ASTDataStmtNode node) {}
    public void visitASTDataStmtSetNode(ASTDataStmtSetNode node) {}
    public void visitASTDataStmtValueNode(ASTDataStmtValueNode node) {}
    public void visitASTDatalistNode(ASTDatalistNode node) {}
    public void visitASTDblConstNode(ASTDblConstNode node) {}
    public void visitASTDeallocateStmtNode(ASTDeallocateStmtNode node) {}
    public void visitASTDeferredCoshapeSpecListNode(ASTDeferredCoshapeSpecListNode node) {}
    public void visitASTDeferredShapeSpecListNode(ASTDeferredShapeSpecListNode node) {}
    public void visitASTDeferredShapeSpecNode(ASTDeferredShapeSpecNode node) {}
    public void visitASTDerivedTypeDefNode(ASTDerivedTypeDefNode node) {}
    public void visitASTDerivedTypeQualifiersNode(ASTDerivedTypeQualifiersNode node) {}
    public void visitASTDerivedTypeSpecNode(ASTDerivedTypeSpecNode node) {}
    public void visitASTDerivedTypeStmtNode(ASTDerivedTypeStmtNode node) {}
    public void visitASTDimensionStmtNode(ASTDimensionStmtNode node) {}
    public void visitASTDoConstructNode(ASTDoConstructNode node) {}
    public void visitASTDummyArgNameNode(ASTDummyArgNameNode node) {}
    public void visitASTEditElementNode(ASTEditElementNode node) {}
    public void visitASTElseConstructNode(ASTElseConstructNode node) {}
    public void visitASTElseIfConstructNode(ASTElseIfConstructNode node) {}
    public void visitASTElseIfStmtNode(ASTElseIfStmtNode node) {}
    public void visitASTElsePartNode(ASTElsePartNode node) {}
    public void visitASTElseStmtNode(ASTElseStmtNode node) {}
    public void visitASTElseWhereConstructNode(ASTElseWhereConstructNode node) {}
    public void visitASTElseWherePartNode(ASTElseWherePartNode node) {}
    public void visitASTElseWhereStmtNode(ASTElseWhereStmtNode node) {}
    public void visitASTEmptyProgramNode(ASTEmptyProgramNode node) {}
    public void visitASTEndAssociateStmtNode(ASTEndAssociateStmtNode node) {}
    public void visitASTEndBlockDataStmtNode(ASTEndBlockDataStmtNode node) {}
    public void visitASTEndBlockStmtNode(ASTEndBlockStmtNode node) {}
    public void visitASTEndCriticalStmtNode(ASTEndCriticalStmtNode node) {}
    public void visitASTEndDoStmtNode(ASTEndDoStmtNode node) {}
    public void visitASTEndEnumStmtNode(ASTEndEnumStmtNode node) {}
    public void visitASTEndForallStmtNode(ASTEndForallStmtNode node) {}
    public void visitASTEndFunctionStmtNode(ASTEndFunctionStmtNode node) {}
    public void visitASTEndIfStmtNode(ASTEndIfStmtNode node) {}
    public void visitASTEndInterfaceStmtNode(ASTEndInterfaceStmtNode node) {}
    public void visitASTEndModuleStmtNode(ASTEndModuleStmtNode node) {}
    public void visitASTEndMpSubprogramStmtNode(ASTEndMpSubprogramStmtNode node) {}
    public void visitASTEndNameNode(ASTEndNameNode node) {}
    public void visitASTEndProgramStmtNode(ASTEndProgramStmtNode node) {}
    public void visitASTEndSelectStmtNode(ASTEndSelectStmtNode node) {}
    public void visitASTEndSelectTypeStmtNode(ASTEndSelectTypeStmtNode node) {}
    public void visitASTEndSubmoduleStmtNode(ASTEndSubmoduleStmtNode node) {}
    public void visitASTEndSubroutineStmtNode(ASTEndSubroutineStmtNode node) {}
    public void visitASTEndTypeStmtNode(ASTEndTypeStmtNode node) {}
    public void visitASTEndWhereStmtNode(ASTEndWhereStmtNode node) {}
    public void visitASTEndfileStmtNode(ASTEndfileStmtNode node) {}
    public void visitASTEntityDeclNode(ASTEntityDeclNode node) {}
    public void visitASTEntryNameNode(ASTEntryNameNode node) {}
    public void visitASTEntryStmtNode(ASTEntryStmtNode node) {}
    public void visitASTEnumDefNode(ASTEnumDefNode node) {}
    public void visitASTEnumDefStmtNode(ASTEnumDefStmtNode node) {}
    public void visitASTEnumeratorDefStmtNode(ASTEnumeratorDefStmtNode node) {}
    public void visitASTEnumeratorNode(ASTEnumeratorNode node) {}
    public void visitASTEquivalenceObjectListNode(ASTEquivalenceObjectListNode node) {}
    public void visitASTEquivalenceObjectNode(ASTEquivalenceObjectNode node) {}
    public void visitASTEquivalenceSetNode(ASTEquivalenceSetNode node) {}
    public void visitASTEquivalenceStmtNode(ASTEquivalenceStmtNode node) {}
    public void visitASTExecutableProgramNode(ASTExecutableProgramNode node) {}
    public void visitASTExitStmtNode(ASTExitStmtNode node) {}
    public void visitASTExplicitCoshapeSpecNode(ASTExplicitCoshapeSpecNode node) {}
    public void visitASTExplicitShapeSpecNode(ASTExplicitShapeSpecNode node) {}
    public void visitASTExternalNameListNode(ASTExternalNameListNode node) {}
    public void visitASTExternalNameNode(ASTExternalNameNode node) {}
    public void visitASTExternalStmtNode(ASTExternalStmtNode node) {}
    public void visitASTFieldSelectorNode(ASTFieldSelectorNode node) {}
    public void visitASTFinalBindingNode(ASTFinalBindingNode node) {}
    public void visitASTFmtSpecNode(ASTFmtSpecNode node) {}
    public void visitASTForallConstructNode(ASTForallConstructNode node) {}
    public void visitASTForallConstructStmtNode(ASTForallConstructStmtNode node) {}
    public void visitASTForallHeaderNode(ASTForallHeaderNode node) {}
    public void visitASTForallStmtNode(ASTForallStmtNode node) {}
    public void visitASTForallTripletSpecListNode(ASTForallTripletSpecListNode node) {}
    public void visitASTFormatEditNode(ASTFormatEditNode node) {}
    public void visitASTFormatIdentifierNode(ASTFormatIdentifierNode node) {}
    public void visitASTFormatStmtNode(ASTFormatStmtNode node) {}
    public void visitASTFormatsepNode(ASTFormatsepNode node) {}
    public void visitASTFunctionArgListNode(ASTFunctionArgListNode node) {}
    public void visitASTFunctionArgNode(ASTFunctionArgNode node) {}
    public void visitASTFunctionInterfaceRangeNode(ASTFunctionInterfaceRangeNode node) {}
    public void visitASTFunctionNameNode(ASTFunctionNameNode node) {}
    public void visitASTFunctionParNode(ASTFunctionParNode node) {}
    public void visitASTFunctionPrefixNode(ASTFunctionPrefixNode node) {}
    public void visitASTFunctionRangeNode(ASTFunctionRangeNode node) {}
    public void visitASTFunctionReferenceNode(ASTFunctionReferenceNode node) {}
    public void visitASTFunctionStmtNode(ASTFunctionStmtNode node) {}
    public void visitASTFunctionSubprogramNode(ASTFunctionSubprogramNode node) {}
    public void visitASTGenericBindingNode(ASTGenericBindingNode node) {}
    public void visitASTGenericNameNode(ASTGenericNameNode node) {}
    public void visitASTGenericSpecNode(ASTGenericSpecNode node) {}
    public void visitASTGoToKwNode(ASTGoToKwNode node) {}
    public void visitASTGotoStmtNode(ASTGotoStmtNode node) {}
    public void visitASTIfConstructNode(ASTIfConstructNode node) {}
    public void visitASTIfStmtNode(ASTIfStmtNode node) {}
    public void visitASTIfThenStmtNode(ASTIfThenStmtNode node) {}
    public void visitASTImageSelectorNode(ASTImageSelectorNode node) {}
    public void visitASTImageSetNode(ASTImageSetNode node) {}
    public void visitASTImplicitSpecNode(ASTImplicitSpecNode node) {}
    public void visitASTImplicitStmtNode(ASTImplicitStmtNode node) {}
    public void visitASTImpliedDoVariableNode(ASTImpliedDoVariableNode node) {}
    public void visitASTImportStmtNode(ASTImportStmtNode node) {}
    public void visitASTInitializationNode(ASTInitializationNode node) {}
    public void visitASTInputImpliedDoNode(ASTInputImpliedDoNode node) {}
    public void visitASTInquireSpecListNode(ASTInquireSpecListNode node) {}
    public void visitASTInquireSpecNode(ASTInquireSpecNode node) {}
    public void visitASTInquireStmtNode(ASTInquireStmtNode node) {}
    public void visitASTIntConstNode(ASTIntConstNode node) {}
    public void visitASTIntentParListNode(ASTIntentParListNode node) {}
    public void visitASTIntentParNode(ASTIntentParNode node) {}
    public void visitASTIntentSpecNode(ASTIntentSpecNode node) {}
    public void visitASTIntentStmtNode(ASTIntentStmtNode node) {}
    public void visitASTInterfaceBlockNode(ASTInterfaceBlockNode node) {}
    public void visitASTInterfaceBodyNode(ASTInterfaceBodyNode node) {}
    public void visitASTInterfaceRangeNode(ASTInterfaceRangeNode node) {}
    public void visitASTInterfaceStmtNode(ASTInterfaceStmtNode node) {}
    public void visitASTIntrinsicListNode(ASTIntrinsicListNode node) {}
    public void visitASTIntrinsicProcedureNameNode(ASTIntrinsicProcedureNameNode node) {}
    public void visitASTIntrinsicStmtNode(ASTIntrinsicStmtNode node) {}
    public void visitASTInvalidEntityDeclNode(ASTInvalidEntityDeclNode node) {}
    public void visitASTIoControlSpecListNode(ASTIoControlSpecListNode node) {}
    public void visitASTIoControlSpecNode(ASTIoControlSpecNode node) {}
    public void visitASTKindParamNode(ASTKindParamNode node) {}
    public void visitASTKindSelectorNode(ASTKindSelectorNode node) {}
    public void visitASTLabelDoStmtNode(ASTLabelDoStmtNode node) {}
    public void visitASTLabelNode(ASTLabelNode node) {}
    public void visitASTLanguageBindingSpecNode(ASTLanguageBindingSpecNode node) {}
    public void visitASTLblDefNode(ASTLblDefNode node) {}
    public void visitASTLblRefListNode(ASTLblRefListNode node) {}
    public void visitASTLblRefNode(ASTLblRefNode node) {}
    public void visitASTLockStmtNode(ASTLockStmtNode node) {}
    public void visitASTLogicalConstNode(ASTLogicalConstNode node) {}
    public void visitASTLoopControlNode(ASTLoopControlNode node) {}
    public void visitASTLowerBoundNode(ASTLowerBoundNode node) {}
    public void visitASTMainProgramNode(ASTMainProgramNode node) {}
    public void visitASTMainRangeNode(ASTMainRangeNode node) {}
    public void visitASTMaskExprNode(ASTMaskExprNode node) {}
    public void visitASTMaskedElseWhereConstructNode(ASTMaskedElseWhereConstructNode node) {}
    public void visitASTMaskedElseWhereStmtNode(ASTMaskedElseWhereStmtNode node) {}
    public void visitASTModuleBlockNode(ASTModuleBlockNode node) {}
    public void visitASTModuleNameNode(ASTModuleNameNode node) {}
    public void visitASTModuleNatureNode(ASTModuleNatureNode node) {}
    public void visitASTModuleNode(ASTModuleNode node) {}
    public void visitASTModuleProcedureStmtNode(ASTModuleProcedureStmtNode node) {}
    public void visitASTModuleStmtNode(ASTModuleStmtNode node) {}
    public void visitASTMpSubprogramRangeNode(ASTMpSubprogramRangeNode node) {}
    public void visitASTMpSubprogramStmtNode(ASTMpSubprogramStmtNode node) {}
    public void visitASTNameNode(ASTNameNode node) {}
    public void visitASTNamedConstantDefNode(ASTNamedConstantDefNode node) {}
    public void visitASTNamedConstantNode(ASTNamedConstantNode node) {}
    public void visitASTNamedConstantUseNode(ASTNamedConstantUseNode node) {}
    public void visitASTNamelistGroupNameNode(ASTNamelistGroupNameNode node) {}
    public void visitASTNamelistGroupObjectNode(ASTNamelistGroupObjectNode node) {}
    public void visitASTNamelistGroupsNode(ASTNamelistGroupsNode node) {}
    public void visitASTNamelistStmtNode(ASTNamelistStmtNode node) {}
    public void visitASTNestedExprNode(ASTNestedExprNode node) {}
    public void visitASTNullifyStmtNode(ASTNullifyStmtNode node) {}
    public void visitASTObjectNameListNode(ASTObjectNameListNode node) {}
    public void visitASTObjectNameNode(ASTObjectNameNode node) {}
    public void visitASTOnlyNode(ASTOnlyNode node) {}
    public void visitASTOpenStmtNode(ASTOpenStmtNode node) {}
    public void visitASTOperatorNode(ASTOperatorNode node) {}
    public void visitASTOptionalParListNode(ASTOptionalParListNode node) {}
    public void visitASTOptionalParNode(ASTOptionalParNode node) {}
    public void visitASTOptionalStmtNode(ASTOptionalStmtNode node) {}
    public void visitASTOutputImpliedDoNode(ASTOutputImpliedDoNode node) {}
    public void visitASTOutputItemList1Node(ASTOutputItemList1Node node) {}
    public void visitASTOutputItemListNode(ASTOutputItemListNode node) {}
    public void visitASTParameterStmtNode(ASTParameterStmtNode node) {}
    public void visitASTParentIdentifierNode(ASTParentIdentifierNode node) {}
    public void visitASTParenthesizedSubroutineArgListNode(ASTParenthesizedSubroutineArgListNode node) {}
    public void visitASTPauseStmtNode(ASTPauseStmtNode node) {}
    public void visitASTPointerFieldNode(ASTPointerFieldNode node) {}
    public void visitASTPointerNameNode(ASTPointerNameNode node) {}
    public void visitASTPointerObjectNode(ASTPointerObjectNode node) {}
    public void visitASTPointerStmtNode(ASTPointerStmtNode node) {}
    public void visitASTPointerStmtObjectNode(ASTPointerStmtObjectNode node) {}
    public void visitASTPositionSpecListNode(ASTPositionSpecListNode node) {}
    public void visitASTPositionSpecNode(ASTPositionSpecNode node) {}
    public void visitASTPrefixSpecNode(ASTPrefixSpecNode node) {}
    public void visitASTPrintStmtNode(ASTPrintStmtNode node) {}
    public void visitASTPrivateSequenceStmtNode(ASTPrivateSequenceStmtNode node) {}
    public void visitASTProcComponentAttrSpecNode(ASTProcComponentAttrSpecNode node) {}
    public void visitASTProcComponentDefStmtNode(ASTProcComponentDefStmtNode node) {}
    public void visitASTProcDeclNode(ASTProcDeclNode node) {}
    public void visitASTProcInterfaceNode(ASTProcInterfaceNode node) {}
    public void visitASTProcedureDeclarationStmtNode(ASTProcedureDeclarationStmtNode node) {}
    public void visitASTProcedureNameListNode(ASTProcedureNameListNode node) {}
    public void visitASTProcedureNameNode(ASTProcedureNameNode node) {}
    public void visitASTProgramNameNode(ASTProgramNameNode node) {}
    public void visitASTProgramStmtNode(ASTProgramStmtNode node) {}
    public void visitASTProtectedStmtNode(ASTProtectedStmtNode node) {}
    public void visitASTRdCtlSpecNode(ASTRdCtlSpecNode node) {}
    public void visitASTRdFmtIdExprNode(ASTRdFmtIdExprNode node) {}
    public void visitASTRdFmtIdNode(ASTRdFmtIdNode node) {}
    public void visitASTRdIoCtlSpecListNode(ASTRdIoCtlSpecListNode node) {}
    public void visitASTRdUnitIdNode(ASTRdUnitIdNode node) {}
    public void visitASTReadStmtNode(ASTReadStmtNode node) {}
    public void visitASTRealConstNode(ASTRealConstNode node) {}
    public void visitASTRenameNode(ASTRenameNode node) {}
    public void visitASTReturnStmtNode(ASTReturnStmtNode node) {}
    public void visitASTRewindStmtNode(ASTRewindStmtNode node) {}
    public void visitASTSFDataRefNode(ASTSFDataRefNode node) {}
    public void visitASTSFDummyArgNameListNode(ASTSFDummyArgNameListNode node) {}
    public void visitASTSFDummyArgNameNode(ASTSFDummyArgNameNode node) {}
    public void visitASTSFExprListNode(ASTSFExprListNode node) {}
    public void visitASTSFExprNode(ASTSFExprNode node) {}
    public void visitASTSFFactorNode(ASTSFFactorNode node) {}
    public void visitASTSFPrimaryNode(ASTSFPrimaryNode node) {}
    public void visitASTSFTermNode(ASTSFTermNode node) {}
    public void visitASTSFVarNameNode(ASTSFVarNameNode node) {}
    public void visitASTSaveStmtNode(ASTSaveStmtNode node) {}
    public void visitASTSavedCommonBlockNode(ASTSavedCommonBlockNode node) {}
    public void visitASTSavedEntityNode(ASTSavedEntityNode node) {}
    public void visitASTScalarMaskExprNode(ASTScalarMaskExprNode node) {}
    public void visitASTScalarVariableNode(ASTScalarVariableNode node) {}
    public void visitASTSectionSubscriptNode(ASTSectionSubscriptNode node) {}
    public void visitASTSelectCaseRangeNode(ASTSelectCaseRangeNode node) {}
    public void visitASTSelectCaseStmtNode(ASTSelectCaseStmtNode node) {}
    public void visitASTSelectTypeBodyNode(ASTSelectTypeBodyNode node) {}
    public void visitASTSelectTypeConstructNode(ASTSelectTypeConstructNode node) {}
    public void visitASTSelectTypeStmtNode(ASTSelectTypeStmtNode node) {}
    public void visitASTSeparateModuleSubprogramNode(ASTSeparateModuleSubprogramNode node) {}
    public void visitASTSignNode(ASTSignNode node) {}
    public void visitASTSpecificBindingNode(ASTSpecificBindingNode node) {}
    public void visitASTStmtFunctionRangeNode(ASTStmtFunctionRangeNode node) {}
    public void visitASTStmtFunctionStmtNode(ASTStmtFunctionStmtNode node) {}
    public void visitASTStopStmtNode(ASTStopStmtNode node) {}
    public void visitASTStringConstNode(ASTStringConstNode node) {}
    public void visitASTStructureComponentNode(ASTStructureComponentNode node) {}
    public void visitASTStructureConstructorNode(ASTStructureConstructorNode node) {}
    public void visitASTSubmoduleBlockNode(ASTSubmoduleBlockNode node) {}
    public void visitASTSubmoduleNode(ASTSubmoduleNode node) {}
    public void visitASTSubmoduleStmtNode(ASTSubmoduleStmtNode node) {}
    public void visitASTSubroutineArgNode(ASTSubroutineArgNode node) {}
    public void visitASTSubroutineInterfaceRangeNode(ASTSubroutineInterfaceRangeNode node) {}
    public void visitASTSubroutineNameNode(ASTSubroutineNameNode node) {}
    public void visitASTSubroutineNameUseNode(ASTSubroutineNameUseNode node) {}
    public void visitASTSubroutineParNode(ASTSubroutineParNode node) {}
    public void visitASTSubroutinePrefixNode(ASTSubroutinePrefixNode node) {}
    public void visitASTSubroutineRangeNode(ASTSubroutineRangeNode node) {}
    public void visitASTSubroutineStmtNode(ASTSubroutineStmtNode node) {}
    public void visitASTSubroutineSubprogramNode(ASTSubroutineSubprogramNode node) {}
    public void visitASTSubscriptNode(ASTSubscriptNode node) {}
    public void visitASTSubscriptTripletNode(ASTSubscriptTripletNode node) {}
    public void visitASTSubstrConstNode(ASTSubstrConstNode node) {}
    public void visitASTSubstringRangeNode(ASTSubstringRangeNode node) {}
    public void visitASTSyncAllStmtNode(ASTSyncAllStmtNode node) {}
    public void visitASTSyncImagesStmtNode(ASTSyncImagesStmtNode node) {}
    public void visitASTSyncMemoryStmtNode(ASTSyncMemoryStmtNode node) {}
    public void visitASTSyncStatNode(ASTSyncStatNode node) {}
    public void visitASTTargetNameNode(ASTTargetNameNode node) {}
    public void visitASTTargetNode(ASTTargetNode node) {}
    public void visitASTTargetObjectNode(ASTTargetObjectNode node) {}
    public void visitASTTargetStmtNode(ASTTargetStmtNode node) {}
    public void visitASTThenPartNode(ASTThenPartNode node) {}
    public void visitASTTypeAttrSpecNode(ASTTypeAttrSpecNode node) {}
    public void visitASTTypeBoundProcedurePartNode(ASTTypeBoundProcedurePartNode node) {}
    public void visitASTTypeDeclarationStmtNode(ASTTypeDeclarationStmtNode node) {}
    public void visitASTTypeGuardStmtNode(ASTTypeGuardStmtNode node) {}
    public void visitASTTypeNameNode(ASTTypeNameNode node) {}
    public void visitASTTypeParamAttrSpecNode(ASTTypeParamAttrSpecNode node) {}
    public void visitASTTypeParamDeclNode(ASTTypeParamDeclNode node) {}
    public void visitASTTypeParamDefStmtNode(ASTTypeParamDefStmtNode node) {}
    public void visitASTTypeParamNameNode(ASTTypeParamNameNode node) {}
    public void visitASTTypeParamSpecNode(ASTTypeParamSpecNode node) {}
    public void visitASTTypeParamValueNode(ASTTypeParamValueNode node) {}
    public void visitASTTypeSpecNode(ASTTypeSpecNode node) {}
    public void visitASTUFExprNode(ASTUFExprNode node) {}
    public void visitASTUFFactorNode(ASTUFFactorNode node) {}
    public void visitASTUFPrimaryNode(ASTUFPrimaryNode node) {}
    public void visitASTUFTermNode(ASTUFTermNode node) {}
    public void visitASTUnaryExprNode(ASTUnaryExprNode node) {}
    public void visitASTUnitIdentifierNode(ASTUnitIdentifierNode node) {}
    public void visitASTUnlockStmtNode(ASTUnlockStmtNode node) {}
    public void visitASTUnprocessedIncludeStmtNode(ASTUnprocessedIncludeStmtNode node) {}
    public void visitASTUpperBoundNode(ASTUpperBoundNode node) {}
    public void visitASTUseNameNode(ASTUseNameNode node) {}
    public void visitASTUseStmtNode(ASTUseStmtNode node) {}
    public void visitASTValueStmtNode(ASTValueStmtNode node) {}
    public void visitASTVarOrFnRefNode(ASTVarOrFnRefNode node) {}
    public void visitASTVariableCommaNode(ASTVariableCommaNode node) {}
    public void visitASTVariableNameNode(ASTVariableNameNode node) {}
    public void visitASTVariableNode(ASTVariableNode node) {}
    public void visitASTVolatileStmtNode(ASTVolatileStmtNode node) {}
    public void visitASTWaitSpecNode(ASTWaitSpecNode node) {}
    public void visitASTWaitStmtNode(ASTWaitStmtNode node) {}
    public void visitASTWhereConstructNode(ASTWhereConstructNode node) {}
    public void visitASTWhereConstructStmtNode(ASTWhereConstructStmtNode node) {}
    public void visitASTWhereRangeNode(ASTWhereRangeNode node) {}
    public void visitASTWhereStmtNode(ASTWhereStmtNode node) {}
    public void visitASTWriteStmtNode(ASTWriteStmtNode node) {}
    public void visitIAccessId(IAccessId node) {}
    public void visitIActionStmt(IActionStmt node) {}
    public void visitIBindEntity(IBindEntity node) {}
    public void visitIBlockDataBodyConstruct(IBlockDataBodyConstruct node) {}
    public void visitIBodyConstruct(IBodyConstruct node) {}
    public void visitICaseBodyConstruct(ICaseBodyConstruct node) {}
    public void visitIComponentDefStmt(IComponentDefStmt node) {}
    public void visitIDataIDoObject(IDataIDoObject node) {}
    public void visitIDataStmtObject(IDataStmtObject node) {}
    public void visitIDeclarationConstruct(IDeclarationConstruct node) {}
    public void visitIDefinedOperator(IDefinedOperator node) {}
    public void visitIDerivedTypeBodyConstruct(IDerivedTypeBodyConstruct node) {}
    public void visitIExecutableConstruct(IExecutableConstruct node) {}
    public void visitIExecutionPartConstruct(IExecutionPartConstruct node) {}
    public void visitIExpr(IExpr node) {}
    public void visitIForallBodyConstruct(IForallBodyConstruct node) {}
    public void visitIInputItem(IInputItem node) {}
    public void visitIInterfaceSpecification(IInterfaceSpecification node) {}
    public void visitIInternalSubprogram(IInternalSubprogram node) {}
    public void visitIModuleBodyConstruct(IModuleBodyConstruct node) {}
    public void visitIModuleSubprogram(IModuleSubprogram node) {}
    public void visitIModuleSubprogramPartConstruct(IModuleSubprogramPartConstruct node) {}
    public void visitIObsoleteActionStmt(IObsoleteActionStmt node) {}
    public void visitIObsoleteExecutionPartConstruct(IObsoleteExecutionPartConstruct node) {}
    public void visitIProcBindingStmt(IProcBindingStmt node) {}
    public void visitIProgramUnit(IProgramUnit node) {}
    public void visitISelector(ISelector node) {}
    public void visitISpecificationPartConstruct(ISpecificationPartConstruct node) {}
    public void visitISpecificationStmt(ISpecificationStmt node) {}
    public void visitIUnsignedArithmeticConst(IUnsignedArithmeticConst node) {}
    public void visitIWhereBodyConstruct(IWhereBodyConstruct node) {}
}