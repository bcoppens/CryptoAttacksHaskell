#include <openssl/ecdsa.h>
#include <openssl/objects.h>
#include <openssl/crypto.h>
#include <openssl/ec.h>
#include <openssl/ecdh.h>
#include <openssl/bn.h>
#include <openssl/evp.h>
#include <openssl/sha.h>
#include <string.h>
#include <stdio.h>

static __inline__ unsigned long long rdtsc(void)
{
  unsigned hi, lo;
  __asm__ __volatile__ ("rdtsc" : "=a"(lo), "=d"(hi));
  return ( (unsigned long long)lo)|( ((unsigned long long)hi)<<32 );
}

static const char* test_string = "This is a message to be signed";

/*
    NID_sect163k1 is the NIST Binary-Curve K-163
    NID_sect163r2 is the NIST Binary-Curve B-163
*/
int main(int argc, char** argv) {
    int ret;
    ECDSA_SIG* sig;
    EC_KEY* eckey = EC_KEY_new();
    long long before, after;
    BN_CTX* ctx = NULL;

    char digest[20];
    int i;

    FILE* theoutputfile = fdopen(1, "w");

    // Digest the string to sign with SHA-1
    SHA1(test_string, strlen(test_string), digest);

    if ((ctx=BN_CTX_new()) == NULL) goto err;

    eckey = EC_KEY_new_by_curve_name(NID_sect163k1);
    if (eckey == NULL)
        goto err;

    // Generate a public/private key pair
    if (!EC_KEY_generate_key(eckey)) goto err;

    for (i = 0; i < 1; i++) {
        // Compute a ECDSA signature of a SHA-1 hash value using ECDSA_do_sign, time how long it takes
        before = rdtsc();
        sig = ECDSA_do_sign(digest, 20, eckey);
        after = rdtsc();

        if (sig == NULL) {
            goto err;
        }

        // We could verify the signature if we wanted (result should be _1_ for a correct result)
        // ret = ECDSA_do_verify(digest, 20, sig, eckey);

        fprintf(theoutputfile, "r: ");
        BN_print_fp(theoutputfile, sig->r);
        fprintf(theoutputfile, "\ns: ");
        BN_print_fp(theoutputfile, sig->s);
        fprintf(theoutputfile, "\n%lld\n", after - before);
        // EC_KEY_print_fp(theoutputfile, eckey, 0 /*??*/);
    }


    // We're done
err:
    ERR_print_errors_fp(stderr);

    if (eckey) EC_KEY_free(eckey);

    return 0;
}
