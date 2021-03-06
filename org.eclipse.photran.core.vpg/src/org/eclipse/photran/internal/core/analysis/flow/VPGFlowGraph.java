/*******************************************************************************
 * Copyright (c) 2010 University of Illinois at Urbana-Champaign and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    UIUC - Initial API and implementation
 *******************************************************************************/
package org.eclipse.photran.internal.core.analysis.flow;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.photran.internal.core.util.Worklist;
import org.eclipse.photran.internal.core.vpg.IVPGNode;
import org.eclipse.photran.internal.core.vpg.NodeRef;
import org.eclipse.photran.internal.core.vpg.VPG;

/**
 * A control flow graph constructed from edges in a VPG.
 *
 * @author Jeff Overbey
 *
 * @param <R> {@link IVPGNode}/{@link NodeRef} type
 * @param <T> node/token type
 * @param <U> flowgraph node type
 */
public abstract class VPGFlowGraph<R extends IVPGNode<T>, T, U>
              extends FlowGraph<U>
{
    private final class NodeFactory
    {
        private final Map<R, FlowGraphNode<U>> nodes = new HashMap<R, FlowGraphNode<U>>();

        private int lastNodeNumber = 0;

        public FlowGraphNode<U> nodeFor(R tokenRef)
        {
            if (nodes.containsKey(tokenRef))
            {
                return nodes.get(tokenRef);
            }
            else
            {
                FlowGraphNode<U> result = new FlowGraphNode<U>(generateNodeName(), map(tokenRef));
                nodes.put(tokenRef, result);
                return result;
            }
        }

        private String generateNodeName()
        {
            return "node" + Integer.toString(++lastNodeNumber); //$NON-NLS-1$
        }

        public FlowGraphNode<U> get(R tokenRef)
        {
            return nodes.get(tokenRef);
        }

        public boolean containsKey(R tokenRef)
        {
            return nodes.containsKey(tokenRef);
        }
    }

    private final NodeFactory nodeFactory;

    protected final VPG<?,?,R> vpg;

    public VPGFlowGraph(VPG<?,?,R> vpg, R entryNodeRef, R exitNodeRef, int controlFlowEdgeType)
    {
        this.vpg = vpg;
        this.nodeFactory = new NodeFactory();
        this.entryNode = nodeFactory.nodeFor(entryNodeRef);
        this.exitNode = nodeFactory.nodeFor(exitNodeRef);

        populate(entryNodeRef, exitNodeRef, controlFlowEdgeType);
    }

    public VPGFlowGraph(VPG<?,?,R> vpg, R entryNodeRef, R exitNodeRef, Enum<?> controlFlowEdgeType)
    {
        this(vpg, entryNodeRef, exitNodeRef, controlFlowEdgeType.ordinal());
    }

    private void populate(R entryNodeRef, R exitNodeRef, int controlFlowEdgeType)
    {
        Worklist<R> worklist = new Worklist<R>(entryNodeRef);

        for (R currentNodeRef : worklist)
        {
            FlowGraphNode<U> currentNode = nodeFactory.get(currentNodeRef);

            for (R successorNodeRef : currentNodeRef.<R>followOutgoing(controlFlowEdgeType))
            {
                if (nodeFactory.containsKey(successorNodeRef))
                {
                    currentNode.connectTo(nodeFactory.get(successorNodeRef));
                }
                else
                {
                    FlowGraphNode<U> successorNode = nodeFactory.nodeFor(successorNodeRef);
                    currentNode.connectTo(successorNode);
                    worklist.add(successorNodeRef);
                }
            }
        }
    }

    protected abstract U map(R tokenRef);
}
