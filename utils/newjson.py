
import json

from charm.toolbox.pairinggroup import PairingGroup
from charm.core.math.pairing import pc_element

group = PairingGroup('SS512')
class ElementEncoder(json.JSONEncoder):
    def default(self, obj):
        if isinstance(obj, pc_element):

            return {
                "_type": "element",
                "value": group.serialize(obj)
            }
        elif isinstance(obj, bytes):
            return {
                "_type": "bytes",
                "value": str(obj, encoding = "utf-8")
            }
        else:
            return super(ElementEncoder, self).default(obj)

class ElementDecoder(json.JSONDecoder):
    def __init__(self, *args, **kwargs):
        json.JSONDecoder.__init__(self, object_hook=self.object_hook, *args, **kwargs)

    def object_hook(self, obj, ):
        if '_type' not in obj:
            return obj
        type = obj['_type']
        if type == 'bytes':
            return bytes(obj['value'], encoding = "utf-8")
        if type == 'element':
            return group.deserialize(obj['value'])
        return obj

def dumps(data,c=ElementEncoder):
    return json.dumps(data,cls=c)

def loads(data,c= ElementDecoder):
    return json.loads(data,cls=c)

# def encode(data,c= ElementEncoder):
#     return json.encode(data,cls=c)
#
# def decode(data,c= ElementDecoder):
#     return json.decode(data,cls=c)
# from newma import MaabeRW15
#
# if __name__ == '__main__':
#
#     group = PairingGroup('SS512')
#     maabe = MaabeRW15(group)
#     gp = maabe.setup()
#     rand = group.random()
#     print(type(rand))
#     data = {'rand': rand}
#     print(data)
#     print(group.serialize(rand))
#     j = json.dumps(data, cls=ElementEncoder, indent=2)
#     print(j)
#     print(json.loads(j, cls=ElementDecoder))

# >>> from newma import MaabeRW15
# >>> from charm.toolbox.pairinggroup import PairingGroup
# >>> from newjson import ElementEncoder, ElementDecoder
# >>> import json
# >>> group = PairingGroup('SS512')
# >>> maabe = MaabeRW15(group)
# >>> gp = maabe.setup()
# >>> rand = group.random()
# >>> print(rand)
# >>> print(group.serialize(rand))
# >>> j = json.dumps({'rand': rand}, cls=ElementEncoder, indent=2)
# >>> print(j)

