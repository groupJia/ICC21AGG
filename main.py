'''
:Authors:         Shashank Agrawal
:Date:            5/2016
'''

from charm.toolbox.pairinggroup import PairingGroup, GT
from bsw07 import BSW07
from ac17 import AC17CPABE


def main():
    # instantiate a bilinear pairing map
    # pairing_group = PairingGroup('MNT224')
    pairing_group = PairingGroup("SS512")
    print("start")
    # AC17 CP-ABE under DLIN (2-linear)
    cpabe = BSW07(pairing_group, 2)

    # run the set up
    (pk, msk) = cpabe.setup()

    # generate a key
    attr_list = ['ONE', 'TWO', 'THREE']
    key = cpabe.keygen(pk, msk, attr_list)

    # choose a random message
    msg = pairing_group.random(GT)
    print(msg)
   
    # generate a ciphertext
    policy_str = '((ONE and THREE) and (TWO OR FOUR))'
    ctxt = cpabe.encrypt(pk, msg, policy_str)
    print(ctxt)

    # decryption
    rec_msg = cpabe.decrypt(pk, ctxt, key)
    print(rec_msg)
    if debug:
        if rec_msg == msg:
            print ("Successful decryption.")
        else:
            print ("Decryption failed.")


if __name__ == "__main__":
    debug = True
    main()