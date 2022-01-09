
from charm.toolbox.pairinggroup import PairingGroup,ZR,G1,G2,GT,pair
from utils.newsecretutils import SecretUtil
import utils.newjson as newjson
from charm.toolbox.ABEnc import ABEnc, Input, Output
import random as mathrandom
import time,sys

# type annotations
mpk_t = { 'g':G1, 'g2':G2, 'h':G1, 'f':G1, 'e_gg_alpha':GT }
msk_t = {'beta':ZR, 'g2_alpha':G2 }
key_t = { 'D0':G2, 'D1':G2, 'D2':G1, 'S':str }
ct_t = { 'C0':GT, 'C1':G1, 'C2':G1, 'C3':G2 }

ret={}
keyV=1
assertExe=True
debug = False
class CPabe_BSW07(ABEnc):
    def __init__(self, groupObj):
        ABEnc.__init__(self)
        global util, group
        util = SecretUtil(groupObj, verbose=False)
        group = groupObj

    @Output(mpk_t, msk_t)    
    def setup(self):
        g, gp = group.random(G1), group.random(G2)
        alpha, beta = group.random(ZR), group.random(ZR)
        # initialize pre-processing for generators
        g.initPP(); gp.initPP()
        
        h = g ** beta
        f = g ** ~beta
        
        e_gg_alpha = pair(g, gp) ** alpha
        
        mpk = { 'g':g, 'g2':gp, 'h':h, 'f':f, 'e_gg_alpha':e_gg_alpha }
        msk = {'beta':beta, 'g2_alpha':gp ** alpha ,"alpha":alpha}
        # ts=time.time()
        # mpk['g']*mpk['g']
        # print(time.time()-ts)

        # ts=time.time()
        # mpk['g2']*mpk['g2']
        # print(time.time()-ts)

        # ts=time.time()
        # e_gg_alpha*e_gg_alpha
        # print(time.time()-ts)
        
        # ts=time.time()
        # pair(g, gp)
        # print(time.time()-ts)
        # print("g",(len(newjson.dumps(g)))/1024.)
        # print((len(newjson.dumps(g)))/1024.)
        return (mpk, msk)
    

    # @Input(mpk_t, msk_t, [str])
    @Output(key_t)
    def keygenAndElgamalEncAndVerify(self, mpk, msk, S, elgamalKeys):
        ts=time.time()
        r = group.random() 
        g_r = (mpk['g2'] ** r)
        
        #original CP-ABE KeyGen algorithm outputs: K=(D0, {D1, D2}) 
        #ED0 <- D0
        ED0 = mpk['g2']**(r+msk['alpha']) #(msk['g2_alpha'] * g_r) ** (1 / msk['beta'])        
        #hard relation: (K, (ED0,{ED1,ED2,ED3}))
        ED1, ED2, ED3 = {}, {},{}        
        attr2r_j={}
        attr2l={}
        for j in S:
            r_j = group.random()
            attr2r_j[j]=r_j
            #ED1 <- D1
            ED1[j] = g_r * (group.hash(j, G2) ** r_j)
            # print(elgamalKeys[j]['pk'])
            l=group.random()
            attr2l[j]=l
            #encrypt D2 to ED2, ED3
            ED2[j]=mpk['g'] ** r_j* (elgamalKeys[j]['pk']**l)
            ED3[j]=mpk['g']**l

        #sigma commitment value (ElGamal ciphertext): ({ED1p, ED2p,ED3p})
        ED1p, ED2p,ED3p = {}, {},{}
        
        attr2r_jp={}
        attr2lp={}
        for j in S:
            r_jp = group.random()
            attr2r_jp[j]=r_jp            
            ED1p[j] = g_r * (group.hash(j, G2) ** r_jp)
            # print(elgamalKeys[j]['pk'])
            lp=group.random()
            attr2lp[j]=lp
            ED2p[j]=mpk['g'] ** r_jp* (elgamalKeys[j]['pk']**lp)
            ED3p[j]=mpk['g']**lp

        # sigma protocol challenge: c
        c=group.hash((ED0,ED1p,ED1p,ED2p,ED2p,ED3p,ED3p), ZR)
        
        attr2r_jtidle={}
        attr2ltidle={}
        attr2AlphaR={}
        for j in S:
            attr2r_jtidle[j]=attr2r_jp[j]-attr2r_j[j]*c
            attr2ltidle[j]=attr2lp[j]-attr2l[j]*c            
            ha=group.hash(j, G2)
            w=group.random(ZR)
            a1=pair(mpk['g'],mpk['g2'])**w
            a2=pair(elgamalKeys[j]['pk'],ha)**w
            # DLEQ challenge value: c2
            c2=group.hash((a1,a2), ZR) 
            z=w-attr2l[j]*c2
            attr2AlphaR[j]={
                "a1":a1,
                "a2":a2,
                "c": c2,
                "z": z,
            }
        ret[keyV]["dis"]+=time.time()-ts
        ts=time.time()    

        # Verify whether the sigma protocol is correct or not
        if assertExe:
            for j in S:
                ha=group.hash(j, G2)
                g=mpk['g']
                gp=mpk['g2']
                z=attr2AlphaR[j]["z"]
                x=pair(ED3[j], gp)
                y=pair(g, ED0)*pair(ED2[j], ha)/mpk['e_gg_alpha']/pair(g,ED1[j])              
                assert(ED2p[j]==g** attr2r_jtidle[j]* (elgamalKeys[j]['pk']**attr2ltidle[j]) * ED2[j]**c)
                assert(ED3p[j]==g** attr2ltidle[j] * ED3[j]**c)                        
                assert(attr2AlphaR[j]["a1"]==pair(g,gp)**z * x**attr2AlphaR[j]["c"] and attr2AlphaR[j]["a2"]==pair(elgamalKeys[j]['pk'],ha)**z * y**attr2AlphaR[j]["c"])
        ret[keyV]["ver"]+=time.time()-ts              
        return {'ED0':ED0, 'ED1':ED1, 'ED2':ED2,'ED3':ED3, 'S':S}
    

    @Input(mpk_t, GT, str)
    @Output(ct_t)
    def encryptAndVerify(self, mpk, M, policy_str):  
        ts=time.time()
        policy = util.createPolicy(policy_str)
        a_list = util.getAttributeList(policy)
        # 
        # (policy)
        s = group.random(ZR)
        shares = util.calculateSharesDict(s, policy)      
        # print("secret0",s)
        sp = group.random(ZR)
        sharesp = util.calculateSharesDict(sp, policy)
        #hard relation: (M, (C0,{C1,C2,C3}))
        C0=(mpk['e_gg_alpha'] ** s) * M
        C1 = mpk['g'] ** s
        C2, C3 = {}, {}
        for i in shares.keys():
            j = util.strip_index(i)
            C2[i] = mpk['g'] ** shares[i]
            C3[i] = group.hash(j, G2) ** shares[i] 
        #sigma protocol commitment (CP-ABE ciphertext): (C0p,{C1p,C2p,C3p})
        Mp=group.random(GT)
        C0p=(mpk['e_gg_alpha'] ** sp) * Mp
        C1p = mpk['g'] ** sp
        C2p, C3p = {}, {}
        for i in sharesp.keys():
            j = util.strip_index(i)
            C2p[i] = mpk['g'] ** sharesp[i]
            C3p[i] = group.hash(j, G2) ** sharesp[i] 
        #sigma protocol challenge: c
        c=group.hash((C0,C0p,C1,C1p,C2,C2p,C3,C3p), ZR)
        stidle=sp-c*s
        # stidle=sp-c*s
        Mtilde = Mp/(M**c)
        sharestidle = {}
        sharestidletest=[stidle]
        for i in sharesp.keys():
            j = util.strip_index(i)
            sharestidle[i] = sharesp[i] - c * shares[i] #% curve_order
            sharestidletest.append(sharesp[i] - c * shares[i])
            # sharestidletest.append(shares[i])
        ret[keyV]["dis"]+=time.time()-ts              
        ts=time.time()

        # Verify whether the sigma protocol is correct or not
        if assertExe:
            assert(C0p==Mtilde* mpk['e_gg_alpha']**stidle * C0**c)
            assert(C1p==mpk['g']**stidle * C1**c)
            for i in sharesp.keys():            
                j = util.strip_index(i)
                assert(C2p[i] == mpk['g']**sharestidle[i] * C2[i]**c )
                assert(C3p[i] == group.hash(j, G2)  ** sharestidle[i] * C3[i]**c)
        
            indexArr = self.tInNrandom(len(a_list)/2+1,len(a_list))
        
            y = util.recoverCoefficients(indexArr)
            z=0
            for i in indexArr:            
                z += sharestidletest[i]*y[i]
            assert(stidle==z)
        ret[keyV]["ver"]+=time.time()-ts              
        return { 'C0':C0,
                 'C1':C1, 'C2':C2, 'C3':C3, 'policy':policy_str}
        
    def tInNrandom(self, t, n) :
        arr = [];
        while True:
            if len(arr) < t:
                num = int(mathrandom.random() * n)
                if num not in arr:
                    arr.append(num)
            else:
                break
        return arr


    @Input(mpk_t, key_t, ct_t)
    @Output(GT)
    def decrypt(self, mpk, key, ct):
        
        policy = util.createPolicy(ct['policy'])
        pruned_list = util.prune(policy, key['S'])
        # if pruned_list == False:
        #     return False
        z = util.newGetCoefficients(policy, pruned_list)
        A = 1 
        for i in pruned_list:
            j = i.getAttributeAndIndex(); k = i.getAttribute()
            A *= ( pair(ct['C2'][j], key['D1'][k]) / pair(key['D2'][k], ct['C3'][j]) ) ** z[j]
        
        return ct['C0'] / (pair(ct['C1'], key['D0']) / A)


def main(nodeNum, t):   
    groupObj = PairingGroup('MNT159')
    #  params = {'SS512':a, 'SS1024':a1, 'MNT159':d159, 'MNT201':d201, 'MNT224':d224, 'BN254':f254 }
    # nodeNum=n

    cpabe = CPabe_BSW07(groupObj)
    # attrs = ['ONE', 'TWO', 'THREE', 'FOUR']
    attrs = ["ATTR%d" % j for j in range(0, nodeNum)]
    # t=int(nodeNum/3)
    access_policy = '(%d of (%s))'%(t,", ".join(attrs))

    # if debug: print("Attributes =>", attrs); print("Policy =>", access_policy)
    print("setup size:=>", "("+str(nodeNum)+","+str('%.2f' % (len(newjson.dumps(groupObj.random(G1)))* nodeNum /1024.))+"kB)")
    (mpk, msk) = cpabe.setup()
    elgamalKeys={}
    for attr in attrs:
        sk=groupObj.random(ZR)
        elgamalKeys[attr]={
            "sk":sk,
            "pk":mpk['g']**sk
        }    
    # ts=time.time()    
    Enckey = cpabe.keygenAndElgamalEncAndVerify(mpk, msk, attrs, elgamalKeys)
    
    rand_msg = groupObj.random(GT)
    # if debug: print("msg =>", rand_msg)
    ct = cpabe.encryptAndVerify(mpk, rand_msg, access_policy)
    print("distribution size:=>", "("+str(nodeNum)+","+str('%.2f' % ((len(newjson.dumps(Enckey))+len(newjson.dumps(ct))-len(ct['policy'])) *2./1024))+"kB)")
    # if debug: print("\n\nCiphertext...\n")
    # groupObj.debug(ct)
    # ret[nodeNum]["dis"]+=time.time()-ts
    # print(nodeNum, time.time()-ts)

    ts=time.time()
    key = {
        "D0": Enckey["ED0"],
        "D1":Enckey["ED1"],
        "D2":{},
        "S":attrs
    }
    for attr in attrs:
        # key["D1"][attr]= Enckey["ED1"][attr]
        key["D2"][attr]= Enckey["ED2"][attr]/(Enckey["ED3"][attr]**elgamalKeys[attr]['sk'])
    
    print("reconstruction size:=>", "("+str(nodeNum)+","+str('%.2f' % (len(newjson.dumps(key["D2"])) *t/nodeNum/1024.))+"kB)")

    rec_msg = cpabe.decrypt(mpk, key, ct)
    # if debug: print("\n\nDecrypt...\n")
    # if debug: print("Rec msg =>", rec_msg)
    ret[keyV]["rec"]+=time.time()-ts              
    assert rand_msg == rec_msg, "FAILED Decryption: message is incorrect"
    # if debug: print("Successful Decryption!!!")

if __name__ == "__main__":
    debug = True
    # assertExe===0? False :True
    asser=lambda x: x if x=="True" else False 
    # assertExe=asser(sys.argv[1])    
    runtimes=1
    Nmax=20
    for n in range(10, Nmax, 10):        
        print("n=",n)
        ret[n]={"dis":0,"ver":0,"rec":0}
        ts=time.time()           
        keyV=n
        for i in range(0, runtimes):
            main(n,int(n/int(sys.argv[1])))
        # print("("+str(n)+", "+ str('%.2f' % (ret[n]["dis"]*1./runtimes))+") ")
    # print(ret)
    dis=""
    ver=""
    rec=""
    # print the time cost for each phase
    for n in range(10, Nmax, 10):        
        dis+="("+str(n)+", "+ str('%.2fs' % (ret[n]["dis"]*1./runtimes))+") "
        ver+="("+str(n)+", "+ str('%.2fs' % (ret[n]["ver"]*1./runtimes))+") "
        rec+="("+str(n)+", "+ str('%.2fs' % (ret[n]["rec"]*1./runtimes))+") "
    print("")
    print("distribution time cost:",dis)
    print("verification time cost:",ver)
    print("reconstruction time cost:",rec)
    
# increasing t
    # runtimes=4
    # n=4
    
    # # for n in range(10, 100, 10):        
    # for t in range(1,int(n/2), 5):
    #     print(t)        
    #     ts=time.time()     
    #     ret[t]={"dis":0,"ver":0,"rec":0}      
    #     keyV=t
    #     for i in range(0, runtimes):
    #         main(n,t)
    #     # print("("+str(n)+", "+ str('%.2f' % (ret[n]["dis"]*1./runtimes))+") ")
    # # print(ret)
    # rec=""
    # for t in range(1, int(n/2), 5):        
    #     # dis+="("+str(n)+", "+ str('%.2f' % (ret[t]["dis"]*1./runtimes))+") "
    #     # ver+="("+str(n)+", "+ str('%.2f' % (ret[t]["ver"]*1./runtimes))+") "
    #     rec+="("+str(t)+", "+ str('%.4f' % (ret[t]["rec"]*1./runtimes))+") "
    # print(rec)


   