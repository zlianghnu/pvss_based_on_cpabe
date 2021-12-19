#!/usr/bin/python

from pyparsing import *
from .newnode import *
import string




def createAttribute(s, loc, toks):
    if toks[0] == '!':
        newtoks = ""
        for i in toks:
            newtoks += i
        return MFNode(newtoks)
    return MFNode(toks[0])  # create


# convert 'attr < value' to a binary tree based on 'or' and 'and'
def parseNumConditional(s, loc, toks):
    # print("print: %s" % toks)
    return MFNode(toks[0])


def printStuff(s, loc, toks):
    # print("print: %s" % toks)
    return toks


def createTree(op, nodes, threshold=1):
    if (op == "or"):
        node = MFNode(OpType.OR)
    elif (op == "and"):
        node = MFNode(OpType.AND)
    elif op == 'of':
        node = MFNode(OpType.THRESHOLD, threshold)
        # for k in range(len(nodes)):
        #     nodes[k] = MFNode(nodes[k])
    else:
        return None
    node.addSubNode(nodes)
    return node


class PolicyParser:
    def __init__(self, verbose=False):
        self.finalPol = self.getBNF()
        self.verbose = verbose
        self.objStack = []
    def pushFirst(self, s, loc, toks):
        self.objStack.append(toks[0])


    def getBNF(self):
        # supported operators => (OR, AND, <
        OperatorOR = Literal("OR").setParseAction(downcaseTokens) | Literal("or")
        OperatorAND = Literal("AND").setParseAction(downcaseTokens) | Literal("and")
        OperatorOF = Literal("OF").setParseAction(downcaseTokens) | Literal("of")
        OperatorWITH = Literal(",").setParseAction(downcaseTokens) | Literal(",")
        Operator = OperatorAND | OperatorOR | OperatorOF | OperatorWITH
        lpar = Literal("(").suppress()
        rpar = Literal(")").suppress()

        BinOperator = Literal("<=") | Literal(">=") | Literal("==") | Word("<>", max=1) | Literal('--')

        # describes an individual leaf node
        leafNode = (Optional("!") + Word(alphanums + '-_./\?!@#$^&*%')).setParseAction(createAttribute)
        # describes expressions such as (attr < value)
        leafConditional = (Word(alphanums) + BinOperator + Word(nums)).setParseAction(parseNumConditional)

        # describes the node concept
        node = leafConditional | leafNode

        expr = Forward()
        term = Forward()
        atom = lpar + expr + rpar | (node).setParseAction(self.pushFirst)
        term = atom + ZeroOrMore((Operator + term).setParseAction(self.pushFirst))
        expr << term + ZeroOrMore((Operator + term).setParseAction(self.pushFirst))
        finalPol = expr  # .setParseAction( printStuff )
        return finalPol

    def evalStack(self, stack):
        op = stack.pop()
        if op in ["or", "and"]:
            op2 = self.evalStack(stack)
            op1 = self.evalStack(stack)
            return createTree(op, [op1, op2][:])
        elif op == 'of':
            values = self.evalStack(stack)
            threshold = self.evalStack(stack)
            return createTree(op, values.copy(), int(str(threshold)))
        elif op == ',':
            op2 = self.evalStack(stack)
            op1 = self.evalStack(stack)
            if type(op1) == list:
                re1 = op1[:]
            else:
                re1 = [op1][:]
            if type(op2) == list:
                re2 = op2[:]
            else:
                re2 = [op2][:]
            re1+=re2
            return re1
        else:
            # Node value (attribute)
            return op

    def parse(self, string):

        del self.objStack[:]
        self.finalPol.parseString(string)
        return self.evalStack(self.objStack)

    def findDuplicates(self, tree, _dict):
        # if tree.left: self.findDuplicates(tree.left, _dict)
        # if tree.right: self.findDuplicates(tree.right, _dict)
        if tree.children:
            for i in tree.children:
                self.findDuplicates(i, _dict)
        if tree.getNodeType() == OpType.ATTR:
            key = tree.getAttribute()
            if _dict.get(key) == None:
                _dict[key] = 1
            else:
                _dict[key] += 1

    def labelDuplicates(self, tree, _dictLabel):
        # if tree.left: self.labelDuplicates(tree.left, _dictLabel)
        # if tree.right: self.labelDuplicates(tree.right, _dictLabel)
        if tree.children:
            for i in tree.children:
                self.labelDuplicates(i, _dictLabel)
        if tree.getNodeType() == OpType.ATTR:
            key = tree.getAttribute()
            if _dictLabel.get(key) != None:
                tree.index = _dictLabel[key]
                _dictLabel[key] += 1

    def prune(self, tree, attributes):
        """given policy tree and attributes, determine whether the attributes satisfy the policy.
           if not enough attributes to satisfy policy, return None otherwise, a pruned list of
           attributes to potentially recover the associated secret.
        """
        (policySatisfied, prunedList) = self.requiredAttributes(tree, attributes)
        #        print("pruned attrs: ", prunedList)
        #        if prunedList:
        #            for i in prunedList:
        #                print("node: ", i)
        if not policySatisfied:
            return policySatisfied
        return prunedList

    def requiredAttributes(self, tree, attrList):
        """ determines the required attributes to satisfy policy tree and returns a list of MFNode
        objects."""
        if tree == None: return 0
        if tree.getNodeType() == OpType.OR or tree.getNodeType() == OpType.AND or tree.getNodeType() == OpType.ATTR:
            Left = tree.getLeft()
            Right = tree.getRight()
            if Left: resultLeft, leftAttr = self.requiredAttributes(Left, attrList)
            if Right: resultRight, rightAttr = self.requiredAttributes(Right, attrList)

            if (tree.getNodeType() == OpType.OR):
                # never return both attributes, basically the first one that matches from left to right
                if resultLeft:
                    sendThis = leftAttr
                elif resultRight:
                    sendThis = rightAttr
                else:
                    sendThis = None

                result = (resultLeft or resultRight)
                if result == False: return (False, sendThis)
                return (True, sendThis)
            if (tree.getNodeType() == OpType.AND):
                if resultLeft and resultRight:
                    sendThis = leftAttr + rightAttr
                elif resultLeft:
                    sendThis = leftAttr
                elif resultRight:
                    sendThis = rightAttr
                else:
                    sendThis = None

                result = (resultLeft and resultRight)
                if result == False: return (False, sendThis)
                return (True, sendThis)

            elif (tree.getNodeType() == OpType.ATTR):
                if (tree.getAttribute() in attrList):
                    return (True, [tree])
                else:
                    return (False, None)
        elif tree.getNodeType() == OpType.THRESHOLD:
            children = tree.getChildren()
            if children is None:
                return
            flag = 0
            re = []
            for i in children:
                result, attr = self.requiredAttributes(i, attrList)
                if result:
                    re += attr
                    flag += 1
                    if flag == tree.threshold:
                        return True, re
            return False, None
        return


# if __name__ == "__main__":
#     # policy parser test cases
#     parser = PolicyParser()
#     attrs = ['1', '3', '7', '8', '5']
#     print("Attrs in user set: ", attrs)
#     # tree1 = parser.parse("(2 of 3^1^5 or 6) and (2 or 3)")
#     tree1 = parser.parse("((2 of (3, 4, 7, 8))) and (5 or 6))")
#     # tree1 = parser.parse("(1 or 2) and (2 and 3))")
#     print("case 1: ", tree1, ", pruned: ", parser.prune(tree1, attrs))

#     tree2 = parser.parse("1 and (1 or 3)")
#     print("case 2: ", tree2, ", pruned: ", parser.prune(tree2, attrs))

#     tree3 = parser.parse("(1 or 2) and (4 or 3)")
#     print("case 3: ", tree3, ", pruned: ", parser.prune(tree3, attrs))

