import string
from charm.toolbox.enum import *

OpType = Enum('OR', 'AND', 'ATTR', 'THRESHOLD', 'CONDITIONAL', 'NONE')


# multi fork
class MFNode:
    def __init__(self, value, threshold=1, children=None):
        # types of node
        #    self.OR = 1
        #    self.AND = 2
        #    self.ATTR = 0
        self.negated = False
        self.index = None
        # OF = '' # anything above 1 and 2
        if isinstance(value, str):
            if value[0] == '!':
                value = value[1:]  # remove but set flag
                self.negated = True
            if value.find('_') != -1:
                val = value.split('_')
                self.index = int(val[1])  # index
                value = val[0]
            self.type = OpType.ATTR
            self.attribute = value.upper()

        elif (value >= OpType.OR and value < OpType.NONE):
            self.type = value
            if self.type == OpType.OR:
                self.threshold = 1
            elif self.type == OpType.AND:
                self.threshold = 2
            elif self.type == OpType.THRESHOLD:
                self.threshold = threshold
            self.attribute = ''
        else:
            self.type = None
            self.attribute = ''

        self.children = children

    def __repr__(self):
        return str(self)

    def __str__(self):
        if self.type == OpType.ATTR:
            if self.negated:
                prefix = '!'
            else:
                prefix = ''
            if self.index != None:
                postfix = '_' + str(self.index)
            else:
                postfix = ''
            return prefix + self.attribute + postfix
        else:
            if self.type == OpType.OR:
                return '(' + str(self.children[0]) + ' or ' + str(self.children[1]) + ')'
            elif self.type == OpType.AND:
                return '(' + str(self.children[0]) + ' and ' + str(self.children[1]) + ')'
            elif self.type == OpType.THRESHOLD:
                temp = []
                for i in self.children:
                    temp.append(str(i))
                re = ', '.join(temp)
                re = str(self.threshold) + ' of (' + re +  ')'
                return re
        return None

    def getAttribute(self):
        if self.type == OpType.ATTR:
            if self.negated:
                prefix = '!'
            else:
                prefix = ''
            return prefix + self.attribute
        return

    def getAttributeAndIndex(self):
        if self.type == OpType.ATTR:
            if self.negated:
                prefix = '!'
            else:
                prefix = ''
            if self.index != None:
                postfix = '_' + str(self.index)
            else:
                postfix = ''

            return prefix + self.attribute + postfix
        return

    def __iter__(self):
        return self

    def __eq__(self, other):
        # print("checking...:", self, str(other))
        if other == None:
            return False
        if type(self) == type(other):
            return self.getAttribute() == other.getAttribute()
        elif type(other) in [str, bytes]:
            return other in self.getAttributeAndIndex()
        elif type(self) in [str, bytes]:
            return self in other.getAttributeAndIndex()
        else:
            raise ValueError('BinNode - invalid comparison.')

    def getLeft(self):
        if self.children is None:
            return None
        return self.children[0]

    def getRight(self):
        if self.children is None:
            return None
        return self.children[1]

    def getChildren(self):
        return self.children

    def getNodeType(self):
        return self.type

    def addSubNode(self, children):
        # set subNodes appropriately
        self.children = children if children != None else None

    # only applies function on leaf nodes
    def traverse(self, function):
        # visit node then traverse left and right
        function(self.type, self)
        if self.children == None:
            return None
        for i in self.children:
            i.traverse(function)
        return None


