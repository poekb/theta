/*
 *  Copyright 2025 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.frontend.transformation.grammar.type;

import static com.google.common.base.Preconditions.checkState;

import hu.bme.mit.theta.c.frontend.dsl.gen.CParser;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.common.logging.Logger.Level;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException;
import hu.bme.mit.theta.frontend.transformation.grammar.IncludeHandlingCBaseVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.expression.UnsupportedInitializer;
import hu.bme.mit.theta.frontend.transformation.grammar.function.FunctionVisitor;
import hu.bme.mit.theta.frontend.transformation.grammar.preprocess.TypedefVisitor;
import hu.bme.mit.theta.frontend.transformation.model.declaration.CDeclaration;
import hu.bme.mit.theta.frontend.transformation.model.statements.CExpr;
import hu.bme.mit.theta.frontend.transformation.model.statements.CInitializerList;
import hu.bme.mit.theta.frontend.transformation.model.statements.CStatement;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.CSimpleType;
import hu.bme.mit.theta.frontend.transformation.model.types.simple.Struct;
import org.antlr.v4.runtime.tree.ParseTree;

import java.util.ArrayList;
import java.util.List;

public class DeclarationVisitor extends IncludeHandlingCBaseVisitor<CDeclaration> {
    private final ParseContext parseContext;
    private final FunctionVisitor functionVisitor;
    private final TypedefVisitor typedefVisitor;
    private final TypeVisitor typeVisitor;
    private final Logger uniqueWarningLogger;

    public DeclarationVisitor(
            ParseContext parseContext,
            FunctionVisitor functionVisitor,
            Logger uniqueWarningLogger) {
        this.parseContext = parseContext;
        this.functionVisitor = functionVisitor;
        this.uniqueWarningLogger = uniqueWarningLogger;
        this.typedefVisitor = new TypedefVisitor(this);
        this.typeVisitor = new TypeVisitor(this, typedefVisitor, parseContext, uniqueWarningLogger);
    }

    public TypedefVisitor getTypedefVisitor() {
        return typedefVisitor;
    }

    public TypeVisitor getTypeVisitor() {
        return typeVisitor;
    }

    public List<CDeclaration> getDeclarations(
            CParser.DeclarationSpecifiersContext declSpecContext,
            CParser.InitDeclaratorListContext initDeclContext) {
        return getDeclarations(declSpecContext, initDeclContext, true);
    }

    /**
     * From a single declaration context and initialization list this function produces the
     * corresponding CDeclarations
     *
     * @param declSpecContext declaration context
     * @param initDeclContext initialization list context
     * @return the corresponding CDeclarations
     */
    public List<CDeclaration> getDeclarations(
            CParser.DeclarationSpecifiersContext declSpecContext,
            CParser.InitDeclaratorListContext initDeclContext,
            boolean getInitExpr) {
        List<CDeclaration> ret = new ArrayList<>();
        CSimpleType cSimpleType = declSpecContext.accept(typeVisitor);
        if (cSimpleType.getAssociatedName() != null) {
            CDeclaration cDeclaration = new CDeclaration(cSimpleType.getAssociatedName());
            cDeclaration.setType(cSimpleType);
            cDeclaration.incDerefCounter(cSimpleType.getPointerLevel());
            ret.add(cDeclaration);
        }
        if (initDeclContext != null) {
            for (CParser.InitDeclaratorContext context : initDeclContext.initDeclarator()) {
                CDeclaration declaration = context.declarator().accept(this);
                CStatement initializerExpression;
                if (context.initializer() != null && getInitExpr) {
                    if (context.initializer().bracedPrimaryExpression() != null) {
                        /*checkState(
                                context.initializer()
                                        .bracedPrimaryExpression()
                                        .initializerList()
                                        .designation()
                                        .isEmpty(),
                                "Initializer list designators not yet implemented!");*/
                        CInitializerList cInitializerList =
                                new CInitializerList(cSimpleType.getActualType(), parseContext);
                        try {

                            //Separation of code, so it can remain fast as well:
                            //if THIS initializerList doesn't contain designator, then the original:
                            if(context.initializer().bracedPrimaryExpression().initializerList().designation().isEmpty()){
                                //---For loop header start without designator---//
                                for (CParser.InitializerContext initializer :
                                    context.initializer()
                                        .bracedPrimaryExpression()
                                        .initializerList()
                                        .initializers) {
                                    //---For loop header ending---//

                                    Expr<?> expr =
                                        cSimpleType
                                            .getActualType()
                                            .castTo(
                                                initializer
                                                    .assignmentExpression()
                                                    .accept(functionVisitor)
                                                    .getExpression());

                                    parseContext.getMetadata().create(expr, "cType", cSimpleType);

                                    cInitializerList.addStatement(
                                        null /* TODO: add designator */,
                                        new CExpr(expr, parseContext));
                                }
                            }
                            //---If we have even one designator we have to navigate through the children of initializerList
                            else{
                                for(ParseTree currentChild : context.initializer().bracedPrimaryExpression().initializerList().children){
                                    // StateMachine logic:
                                    // every init list with designator looks like this:
                                    // { .y= 3.6, 123, .x =12.4 }
                                    // With the braces we don't have to struggle now
                                    // So now the children of initializerList should look like this as the parser does it's thing:
                                    // [0] -> .y=   [1] -> 3.6   [2] -> ,   [3] -> 123   [4] -> ,   [5] -> .x=   [6] -> 12.4
                                    // We have to watch out for the commas as well
                                    // If we see a value then we can do 4 things:
                                    // 1) there were no prior designators, then a simple assigment to the next one
                                    // 2) there were designator but not for this--> we should see which comes
                                    // 3) there were designator and there were no comma so the value should be assigned to the field according to the last designator
                                    // 4) if more value than fields -> exception (TODO: ask if it needs to be addressed)

                                    if(currentChild instanceof CParser.DesignationContext){
                                        //If it is a designationContext (.xyz=) then we will trim it to xyz
                                        String designatedField = currentChild.getText().replace(".", "").replace("=","").trim();
                                        //Check whether it is a struct indeed
                                        CSimpleType actType = cSimpleType.getBaseType();
                                        checkState(actType instanceof Struct, "Designators can be used only with structs");
                                        //Get the field from the struct
                                        CDeclaration test = ((Struct) actType).getFields().get(designatedField);
                                        //And then we check whether there is really a field like this in the struct
                                        checkState(test != null, "There is no field called like " + designatedField);

                                        //TODO: Now use this searched designated field :)
                                        //TODO: We should save the designated field, in case we have mixed initList
                                    }
                                }
                            }

                            initializerExpression = cInitializerList;
                        } catch (NullPointerException e) {
                            initializerExpression =
                                    new CExpr(new UnsupportedInitializer(), parseContext);
                            parseContext
                                    .getMetadata()
                                    .create(
                                            initializerExpression.getExpression(),
                                            "cType",
                                            cSimpleType);
                        }
                    } else {
                        initializerExpression =
                                context.initializer()
                                        .assignmentExpression()
                                        .accept(functionVisitor);
                    }
                    declaration.setInitExpr(initializerExpression);
                }
                declaration.setType(cSimpleType);
                ret.add(declaration);
            }
        }
        if (cSimpleType.getAssociatedName() == null
                && initDeclContext != null
                && initDeclContext.initDeclarator().size() > 0) {
            ret.get(0).incDerefCounter(cSimpleType.getPointerLevel());
        }
        return ret;
    }

    @Override
    public CDeclaration visitOrdinaryParameterDeclaration(
            CParser.OrdinaryParameterDeclarationContext ctx) {
        CSimpleType cSimpleType = ctx.declarationSpecifiers().accept(typeVisitor);
        CDeclaration declaration = ctx.declarator().accept(this);
        declaration.setType(cSimpleType);
        return declaration;
    }

    @Override
    public CDeclaration visitStructDeclaratorSimple(CParser.StructDeclaratorSimpleContext ctx) {
        return ctx.declarator().accept(this);
    }

    @Override
    public CDeclaration visitStructDeclaratorConstant(CParser.StructDeclaratorConstantContext ctx) {
        throw new UnsupportedFrontendElementException("Not yet supported!");
    }

    @Override
    public CDeclaration visitAbstractParameterDeclaration(
            CParser.AbstractParameterDeclarationContext ctx) {
        CSimpleType cSimpleType = ctx.declarationSpecifiers2().accept(typeVisitor);
        checkState(ctx.abstractDeclarator() == null, "Abstract declarators not yet supported!");
        return new CDeclaration(cSimpleType);
    }

    @Override
    public CDeclaration visitDeclarator(CParser.DeclaratorContext ctx) {
        checkState(
                ctx.pointer() == null || ctx.pointer().typeQualifierList().size() == 0,
                "pointers should not have type qualifiers! (not yet implemented)");
        // checkState(ctx.gccDeclaratorExtension().size() == 0, "Cannot do anything with
        // gccDeclaratorExtensions!");
        CDeclaration decl = ctx.directDeclarator().accept(this);

        if (ctx.pointer() != null) {
            int size = ctx.pointer().stars.size();
            decl.incDerefCounter(size);
        }
        return decl;
    }

    @Override
    public CDeclaration visitDirectDeclaratorId(CParser.DirectDeclaratorIdContext ctx) {
        return new CDeclaration(ctx.getText());
    }

    @Override
    public CDeclaration visitDirectDeclaratorBraces(CParser.DirectDeclaratorBracesContext ctx) {
        return ctx.declarator().accept(this);
    }

    @Override
    public CDeclaration visitDirectDeclaratorArray1(CParser.DirectDeclaratorArray1Context ctx) {
        checkState(
                ctx.typeQualifierList() == null,
                "Type qualifiers inside array declarations are not yet implemented.");

        CDeclaration decl = ctx.directDeclarator().accept(this);
        if (ctx.assignmentExpression() != null) {
            decl.addArrayDimension(ctx.assignmentExpression().accept(functionVisitor));
        } else {
            decl.addArrayDimension(null);
        }
        return decl;
    }

    @Override
    public CDeclaration visitDirectDeclaratorArray2(CParser.DirectDeclaratorArray2Context ctx) {
        throw new UnsupportedFrontendElementException("Not yet implemented!");
    }

    @Override
    public CDeclaration visitDirectDeclaratorArray3(CParser.DirectDeclaratorArray3Context ctx) {
        throw new UnsupportedFrontendElementException("Not yet implemented!");
    }

    @Override
    public CDeclaration visitDirectDeclaratorArray4(CParser.DirectDeclaratorArray4Context ctx) {
        throw new UnsupportedFrontendElementException("Not yet implemented!");
    }

    @Override
    public CDeclaration visitDirectDeclaratorFunctionDecl(
            CParser.DirectDeclaratorFunctionDeclContext ctx) {
        CDeclaration decl = ctx.directDeclarator().accept(this);
        if (!(ctx.parameterTypeList() == null || ctx.parameterTypeList().ellipses == null)) {
            uniqueWarningLogger.write(Level.INFO, "WARNING: variable args are not supported!\n");
            decl.setFunc(true);
            return decl;
        }
        if (ctx.parameterTypeList() != null) {
            for (CParser.ParameterDeclarationContext parameterDeclarationContext :
                    ctx.parameterTypeList().parameterList().parameterDeclaration()) {
                decl.addFunctionParam(parameterDeclarationContext.accept(this));
            }
        }
        decl.setFunc(true);
        return decl;
    }

    @Override
    public CDeclaration visitDirectDeclaratorBitField(CParser.DirectDeclaratorBitFieldContext ctx) {
        throw new UnsupportedOperationException("Not yet implemented!");
    }
}
