/*******************************************************************************
 * Copyright (c) 2015 Actilon Consulting and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     Jeff Overbey - Initial API and implementation
 *******************************************************************************/
package org.eclipse.photran.internal.tests.parser;

import java.io.FileNotFoundException;
import java.io.IOException;

import junit.framework.Test;

public class ParseHPExtensionsFreeTestFiles
{
    public static Test suite() throws FileNotFoundException, IOException
    {
        return new MultiTestSuite("hpextensions_tests_free", false, true) {};
    }
}