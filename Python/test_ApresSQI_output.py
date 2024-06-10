from kummer_verification import verification
from kummer_arithmetic import squared_kummer_from_squared_thetas
from globals import set_prime

p = 507227047723007
set_prime(p)

mu_K_A, resp, mu_K_2 = (
    [
        400651756096775, 85816326267395], [
            [
                457093238310817, 102432803471130, 457221404838757, 416696996201803], [
                    439534055631293, 229598597848935, 215829955345377, 18143117774758], [
                        -56446781900421, -107169996459154, 270465289815694, 484452378548983], [
                            -465894771759296, -164442188935886, 72445280146305, 489156466655763], [
                                -208651064569975, -81912450346275, 215580947434566, 2304654971016], [
                                    308474540025485, 402463320410289, 398648087215081, 438845425239082], [
                                        54612367267993, 163176245251094, 100197967256458, 316901579698415]], [
                                            65951033793180, 293818047844279])

mu_K_A += [1, 1]
mu_K_2 += [1, 1]

K_A = squared_kummer_from_squared_thetas(mu_K_A)
K_2 = squared_kummer_from_squared_thetas(mu_K_2)

sigma = [K_2, resp]

verification(K_A, sigma)