from charm.toolbox.pairinggroup import PairingGroup, ZR, G1, GT, pair
from charm.toolbox.secretutil import SecretUtil
#from charm.toolbox.msp import MSP
from charm.toolbox.ABEncMultiAuth import ABEncMultiAuth
import re


# def merge_dicts(*dict_args):
#     """
#     Given any number of dicts, shallow copy and merge into a new dict,
#     precedence goes to key value pairs in latter dicts.
#     """
#     result = {}
#     for dictionary in dict_args:
#         result.update(dictionary)
#     return result


class RMABE(object):

    def __init__(self, groupObj, verbose=False):

        ABEncMultiAuth.__init__(self)
        self.util = SecretUtil(groupObj, verbose=False)
        #self.msp = MSP(groupObj, verbose=False)
        self.group = groupObj

    def setup(self):
        '''global setup(CA)'''

        g = self.group.random(G1)
        H = lambda x: self.group.hash(x, G1)
        F = lambda x: self.group.hash(x, G1)
        egg = pair(g, g)
        gp = {'g': g, 'H': H, 'F': F, 'egg': egg}
        return gp

    def unpack_attribute(self, attribute):
        parts = re.split(r"[@_]", attribute)
        assert len(parts) > 1, "No @ char in [attribute@authority] name"
        return parts[0], parts[1], None if len(parts) < 3 else parts[2]

    def attr_setup(self, gp, attributes):

        vx = {}
        PK_attr = {}
        for attr in attributes:
            v = self.group.random(ZR)
            vx[attr] = v
            PK_attr[attr] = gp['g'] ** v * gp['F'](attr)

        return vx, PK_attr

    def authsetup(self, gp, name):
        alpha = self.group.random(ZR)
        beta = self.group.random(ZR)

        egg_alpha = gp['egg'] ** alpha
        g_alpha = gp['g'] ** alpha
        g_beta = gp['g'] ** beta

        pk = {'name': name,'egg_alpha': egg_alpha, 'g_alpha': g_alpha, 'g_beta':g_beta}
        sk = {'name': name, 'alpha': alpha, 'beta':beta}
        return pk, sk

    def keygen(self, gid, gp, sk, attribute, PK_attr):

        _, auth, _ = self.unpack_attribute(attribute)
        assert auth == sk['name'], "Invalid authority name"
        t = self.group.random(ZR)
        K1 = (gp['g'] ** sk['alpha']) * ((gp['H'](gid)) ** sk['beta']) * (PK_attr[attribute] ** t)
        K2 = gp['g'] ** (t)
        K3 = gid


        return {'K1': K1, 'K2': K2, 'K3': K3}

    def multi_attributes_keygen(self, gp, sk, gid, attributes, PK_attr):
        uk = {}
        for attribute in attributes:
            uk[attribute] = self.keygen(gid, gp, sk, attribute, PK_attr)
        return uk

    def encrypt(self, gp, pks, mess, policy_str, PK_attr):

        policy = self.util.createPolicy(policy_str)
        attrs = self.util.getAttributeList(policy)
        # print(attrs)

        # for i in attrs:
        #     print(i.getAttribute())

        s = self.group.random(ZR)
        # w = self.group.init(ZR, 0)

        secret_shares = self.util.calculateSharesDict(s, policy)
        # zero_shares = self.util.calculateSharesDict(w, policy)
        # print(secret_shares)
        # print(zero_shares)

        # for i in secret_shares:
        #     print(i)
        #     print(secret_shares[i])

        C0 = mess * (gp['egg'] ** s)
        C1, C2, C3, C4 = {}, {}, {}, {}

        for i in attrs:
            attribute_name, authority_name, _ = self.unpack_attribute(i)
            attr = "%s@%s" % (attribute_name, authority_name)
            tx = self.group.random(ZR)
            C1[i] = gp['egg'] ** secret_shares[i] * pks[authority_name]['egg_alpha'] ** (tx)
            C2[i] = gp['g'] ** ((-tx))
            C3[i] = pks[authority_name]['g_beta'] ** (tx)
            C4[i] = PK_attr[attr] ** tx
        return {'policy': policy_str, 'C0': C0, 'C1': C1, 'C2': C2, 'C3': C3, 'C4': C4}, {
            'secret_shares': secret_shares, 's': s}

    def decrypt(self, gp, sk, ct):

        policy = self.util.createPolicy(ct['policy'])
        coefficients = self.util.getCoefficients(policy)
        pruend_list = self.util.prune(policy, sk['keys'].keys())
        # print(pruend_list)

        if not pruend_list:
            raise Exception("You don't have the required attributes for decryption!")

        B = self.group.init(GT, 1)
        for i in range(len(pruend_list)):
            y = pruend_list[i].getAttributeAndIndex()
            x = pruend_list[i].getAttribute()

            B *= (ct['C1'][y] * pair(gp['H'](sk['keys'][x]['K3']), ct['C3'][y]) * pair(ct['C4'][y], sk['keys'][x]['K2']) * pair(ct['C2'][y] , sk['keys'][x]['K1'])) ** coefficients[y]

        return ct['C0'] / B

    def gentransformkey(self, gp, ct, sk):

        TK = {}
        RK = {}
        z = self.group.random(ZR)

        for i in sk['keys']:
            attribute = i
            K1 = sk['keys'][i]['K1']
            K2 = sk['keys'][i]['K2']
            tk1 = K1 ** (1 / z)
            tk2 = K2 ** (1 / z)
            TK[attribute] = {'tk1': tk1, 'tk2': tk2}

        RK = {'z': z}

        policy = self.util.createPolicy(ct['policy'])
        attrs = self.util.getAttributeList(policy)
        C1_, C3_ = {}, {}
        for i in attrs:
            C1_[i] = ct['C1'][i] ** (1 / z)
            C3_[i] = ct['C3'][i] ** (1 / z)

        CT_ = {'policy': ct['policy'], 'C0': ct['C0'], 'C1': C1_,
               'C2': ct['C2'], 'C3': C3_, 'C4': ct['C4']}
        return TK, RK, CT_

    def transform(self, gp, CT_, gid, TK):

        policy = self.util.createPolicy(CT_['policy'])
        coefficients = self.util.getCoefficients(policy)
        pruend_list = self.util.prune(policy, TK.keys())

        if not pruend_list:
            raise Exception(
                "You don't have the required attributes for decryption!")

        B = self.group.init(GT, 1)
        for i in range(len(pruend_list)):
            x = pruend_list[i].getAttribute()
            y = pruend_list[i].getAttributeAndIndex()

            B *= (CT_['C1'][y] * pair(gp['H'](gid), CT_['C3'][y]) * pair(TK[x]['tk1'], CT_['C2'][y]) * pair(TK[x]['tk2'], CT_['C4'][y])) ** coefficients[y]

        CT_OUT = {'C0': CT_['C0'], 'D': B}
        return CT_OUT

    def outsourcingDecrypt(self, gp, CT_OUT, RK):
        return CT_OUT['C0'] / (CT_OUT['D'] ** RK['z'])

    def trace(self, gp, sk, pks, PK_attr):

        for i in sk['keys']:
            attribute = i

            K1 = sk['keys'][i]['K1']
            K2 = sk['keys'][i]['K2']
            K3 = sk['keys'][i]['K3']

            if (not K1) or (not K2) or (not K3):
                raise Exception("The key is not complete!")

            # if (K1 not in G1) or (K2 not in G1) or (K3 not in ZR):
            #     raise Exception("The key is not satisfied the type of key")

            _, authority_name, _ = self.unpack_attribute(attribute)

            if pair(K1, gp['g']) == pks[authority_name]['egg_alpha'] * pair(gp['H'](K3), pks[authority_name]['g_beta']) * pair(PK_attr[attribute], K2):
                return 'The key has been leaked! The leaker\'s gid is %d' % K3

        return 'error'

    def policycompare(self, attr1, attr2):

        I1A_ = []
        I2A_ = []
        I3A_ = []
        # num: attr1中的属性个数
        num = len(attr1)
        flag = [0] * num
        for i in range(len(attr2)):
            attribute_name, authority_name, _ = self.unpack_attribute(attr2[i])
            attribute = "%s@%s" % (attribute_name, authority_name)
            cnt = 0
            flag_ = 0
            for j in range(len(attr1)):
                attr_name, auth_name, _ = self.unpack_attribute(attr1[j])
                attr = "%s@%s" % (attr_name, auth_name)
                if attribute == attr:
                    if flag[j] == 1:
                        cnt += 1
                        continue
                    else:
                        I1A_.append((attr2[i], attr1[j]))
                        flag[j] = 1
                        cnt = 0
                        flag_ = 1
                        break
            if flag_ == 0:
                if cnt != 0:
                    for j in range(len(attr1)):
                        attr_name, auth_name, _ = self.unpack_attribute(attr1[j])
                        attr = "%s@%s" % (attr_name, auth_name)
                        if attribute == attr:
                            I2A_.append((attr2[i], attr1[j]))
                            break
                else:
                    I3A_.append((attr2[i], None))

        return I1A_, I2A_, I3A_

    def PUKGen(self, gp, pk, shares_info, policy_str, new_policy_str, PK_attr):

        policy = self.util.createPolicy(policy_str)
        attrs = self.util.getAttributeList(policy)
        # ['STUDENT@UT_0', 'PROFESSOR@OU', 'STUDENT@UT_1', 'MASTERS@OU']

        new_policy = self.util.createPolicy(new_policy_str)
        new_attrs = self.util.getAttributeList(new_policy)

        s = shares_info['s']
        secret_shares = shares_info['secret_shares']
        # zero_shares = shares_info['zero_shares']

        secret_shares_ = self.util.calculateSharesDict(s, new_policy)
        # zero_shares_ = self.util.calculateSharesDict(0, new_policy)

        I1A_, I2A_, I3A_ = self.policycompare(attrs, new_attrs)

        Class1, Class2, Class3 = {}, {}, {}

        for i in new_attrs:
            attr_name, auth_name, _ = self.unpack_attribute(i)
            attr = "%s@%s" % (attr_name, auth_name)

            if (i, None) in I3A_:
                r = self.group.random(ZR)
                uk1 = gp['g'] ** secret_shares_[i] * pk[auth_name]['g_alpha'] ** (r)
                uk2 = gp['g'] ** (-r)
                uk3 = pk[auth_name]['g_beta'] ** r
                uk4 = PK_attr[attr] ** r

                Class3[i] = {'uk1': uk1, 'uk2': uk2, 'uk3': uk3, 'uk4': uk4}

                continue

            for j in attrs:
                if (i, j) in I1A_:
                    uk1 = gp['g'] ** (secret_shares_[i] - secret_shares[j])
                    # uk2 = gp['g'] ** (zero_shares_[i] - zero_shares[j])
                    Class1[i] = {'uk1': uk1, 'placed_attr':j}
                    break
                elif (i, j) in I2A_:
                    a = self.group.random(ZR)
                    uk1 = gp['g'] ** (secret_shares_[i] - a * secret_shares[j])
                    # uk2 = gp['g'] ** (zero_shares_[i] - a * zero_shares[j])
                    Class2[i] = {'a': a, 'uk1': uk1, 'placed_attr':j}
                    break

        return Class1, Class2, Class3

    def PCTUpdate(self, gp, CT, Class1, Class2, Class3, new_policy_str):

        new_policy = self.util.createPolicy(new_policy_str)
        new_attrs = self.util.getAttributeList(new_policy)

        C0_ = CT['C0']
        C1_, C2_, C3_, C4_= {}, {}, {}, {}

        for i in new_attrs:
            if i in Class1:
                j = Class1[i]['placed_attr']
                C1_[i] = CT['C1'][j] * pair(gp['g'], Class1[i]['uk1'])
                C2_[i] = CT['C2'][j]
                C3_[i] = CT['C3'][j]
                C4_[i] = CT['C4'][j]

            elif i in Class2:
                j = Class2[i]['placed_attr']
                C1_[i] = CT['C1'][j] ** Class2[i]['a'] * pair(gp['g'], Class2[i]['uk1'])
                C2_[i] = CT['C2'][j] ** Class2[i]['a']
                C3_[i] = CT['C3'][j] ** Class2[i]['a']
                C4_[i] = CT['C4'][j] ** Class2[i]['a']

            elif i in Class3:
                C1_[i] = pair(gp['g'], Class3[i]['uk1'])
                C2_[i] = Class3[i]['uk2']
                C3_[i] = Class3[i]['uk3']
                C4_[i] = Class3[i]['uk4']

        return {'policy': new_policy_str, 'C0': C0_, 'C1': C1_, 'C2': C2_, 'C3': C3_, 'C4': C4_}

    def GenUpdateKey(self, gp, undo_attribute, vx):
        # 用户属性撤销
        v_ = self.group.random(ZR)
        v = vx[undo_attribute]
        AUK = (v_ - v)

        return AUK

    def KeyUpdate(self, gp, user_keys, undo_attribute, AUK):

        user_keys['keys'][undo_attribute]['K1'] = user_keys['keys'][undo_attribute]['K1'] * \
                                                  user_keys['keys'][undo_attribute]['K2'] ** AUK

        return user_keys

    def CTupdate(self, gp, ct, undo_attribute, AUK):

        policy = self.util.createPolicy(ct['policy'])
        attrs = self.util.getAttributeList(policy)

        for i in attrs:

            attr_name, auth_name, _ = self.unpack_attribute(i)

            attr = "%s@%s" % (attr_name, auth_name)

            if attr == undo_attribute:
                ct['C4'][i] = ct['C4'][i] * (1 / ct['C2'][i]) ** AUK

        return ct


# def main():
#     group = PairingGroup('SS512')
#     maabe = RMABE(group)
#     public_parameters = maabe.setup()

#     (public_key1, secret_key1) = maabe.authsetup(public_parameters, 'UT')
#     (public_key2, secret_key2) = maabe.authsetup(public_parameters, 'OU')
#     public_keys = {'UT': public_key1, 'OU': public_key2}

#     attributes = ['STUDENT@UT', 'PHD@UT', 'STUDENT@OU', 'PROFESSOR@OU', 'MASTERS@OU']
#     vx, PK_attr = maabe.attr_setup(public_parameters, attributes)

#     user_name = "bob"
#     gid = group.random(ZR)
#     user_attributes1 = ['STUDENT@UT', 'PHD@UT']
#     user_attributes2 = ['STUDENT@OU']
#     user_keys1 = maabe.multi_attributes_keygen(public_parameters, secret_key1, gid, user_attributes1, PK_attr)
#     user_keys2 = maabe.multi_attributes_keygen(public_parameters, secret_key2, gid, user_attributes2, PK_attr)
#     user_keys = {'user_name': user_name, 'GID': gid, 'keys': merge_dicts(user_keys1, user_keys2)}

#     user2_name = "alice"
#     gid2 = group.random(ZR)
#     user2_attributes1 = ['STUDENT@UT', 'PHD@UT']
#     user2_attributes2 = ['MASTERS@OU']
#     user2_keys1 = maabe.multi_attributes_keygen(public_parameters, secret_key1, gid, user2_attributes1, PK_attr)
#     user2_keys2 = maabe.multi_attributes_keygen(public_parameters, secret_key2, gid, user2_attributes2, PK_attr)
#     user2_keys = {'user_name': user2_name, 'GID': gid2, 'keys': merge_dicts(user2_keys1, user2_keys2)}

#     message = group.random(GT)

#     access_policy = '(STUDENT@UT and PHD@UT) and (STUDENT@OU or MASTERS@OU)'
#     cipher_text, shares_info = maabe.encrypt(public_parameters, public_keys, message, access_policy, PK_attr)

#     decrypted_message = maabe.decrypt(public_parameters, user_keys, cipher_text)
#     assert decrypted_message == message

#     decrypted_message_alice = maabe.decrypt(public_parameters, user2_keys, cipher_text)
#     assert decrypted_message_alice == message

#     TK, RK, cipher_text_ = maabe.gentransformkey(public_parameters, cipher_text, user_keys)
#     CT_OUT = maabe.transform(public_parameters, cipher_text_, gid, TK)
#     outsourcing_decrypted_message = maabe.outsourcingDecrypt(public_parameters, CT_OUT, RK)

#     assert outsourcing_decrypted_message == message

#     print(maabe.trace(public_parameters, user_keys, public_keys, PK_attr))

#     # print(maabe.trace(public_parameters, user_keys, public_keys))

#     # attr1 = ['STUDENT@UT_0', 'PROFESSOR@OU', 'STUDENT@UT_1', 'MASTERS@OU']

#     # attr2 = ['STUDENT@UT_0', 'PROFESSOR@OU', 'STUDENT@UT_1', 'STUDENT@UT_2', 'MASTERS@OT']

#     # print(maabe.policycompare(attr1, attr2))

#     new_policy = '(STUDENT@UT and PHD@UT) and (STUDENT@UT or MASTERS@OU)'

#     Class1, Class2, Class3 = maabe.PUKGen(public_parameters, public_keys, shares_info, access_policy, new_policy,
#                                             PK_attr)

#     CT_ = maabe.PCTUpdate(public_parameters, cipher_text, Class1, Class2, Class3, new_policy)

#     decrypted_message_new = maabe.decrypt(public_parameters, user_keys, CT_)
#     assert decrypted_message_new == message

#     undo_attribute = 'PHD@UT'
#     AUK = maabe.GenUpdateKey(public_parameters, undo_attribute, vx)
#     maabe.KeyUpdate(public_parameters, user2_keys, undo_attribute, AUK)
#     maabe.CTupdate(public_parameters, cipher_text, undo_attribute, AUK)
#     # undo_attribute = 'STUDENT@UT'
#     # KUK, CUK = maabe.GenUpdateKey(public_parameters, secret_key1, undo_attribute, vx)
#     # maabe.KeyUpdate(public_parameters, user_keys, undo_attribute, KUK)
#     # maabe.CT_undo_update(public_parameters, cipher_text, undo_attribute, CUK)

#     decrypted_message_undo = maabe.decrypt(public_parameters, user2_keys, cipher_text)
#     assert decrypted_message_undo == message

#     decrypted_message_bob_undo = maabe.decrypt(public_parameters, user_keys, cipher_text)
#     assert decrypted_message_bob_undo == message

# main()
