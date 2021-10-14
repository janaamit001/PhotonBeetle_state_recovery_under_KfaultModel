#ifdef _MSC_VER
#define _CRT_SECURE_NO_WARNINGS
#endif

#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include <time.h>

#include "crypto_aead.h"
#include "photon.h"
#include "api.h"

#define KAT_SUCCESS          0
#define KAT_FILE_OPEN_ERROR -1
#define KAT_DATA_ERROR      -3
#define KAT_CRYPTO_FAILURE  -4

#define MAX_FILE_NAME				256
#define MAX_MESSAGE_LENGTH			32
#define MAX_ASSOCIATED_DATA_LENGTH	32
#define sboxSize 16
#define number 2

//const unsigned char WORDFILTER = 0xF;

extern uint8_t st[8][8], st1[8][8], st2[8][8], st3[8][8], st4[8][8], st5[8][8];
extern unsigned char ftag[ 16 ], nfstate[32], fstate[32];
unsigned char s[16] = {0xc, 5, 6, 0xb, 9, 0, 0xa, 0xd, 3, 0xe, 0xf, 8, 4, 7, 1, 2};

void init_buffer(unsigned char *buffer, unsigned long long numbytes);

void fprint_bstr(FILE *fp, const char *label, const unsigned char *data, unsigned long long length);

int generate_test_vectors();

int main()
{
	int ret = generate_test_vectors();

	if (ret != KAT_SUCCESS) {
		fprintf(stderr, "test vector generation failed with code %d\n", ret);
	}

	return ret;
}


/*unsigned char FieldMult(unsigned char a, unsigned char b)
{
	const unsigned char ReductionPoly = 0x3;
	unsigned char x = a, ret = 0;
	int i;
	for(i = 0; i < 4; i++) {
		if((b>>i)&1) ret ^= x;
		if(x&0x8) {
			x <<= 1;
			x ^= ReductionPoly;
		}
		else x <<= 1;
	}
	return ret&WORDFILTER;
}*/


void print( unsigned char *m ) {

	printf("Ciphertext::\n");
	for( short i = 0; i < 32; ++i )
		printf("%x ", m[ i ]);
		
	printf("\n\n");
	
	printf("Tag::\n");
	for( short i = 32; i < 48; ++i )
		printf("%02x ", m[ i ]);
		
	printf("\n\n");

	return;
}


void copy_ciphertext( unsigned char ct1[], unsigned char ct[] ) {

	for( short i = 0; i < 48; ++i )
		ct1[ i ] = ct[ i ];

	return;
}

void xor_of_diff_tag( uint8_t state[8][8], unsigned char ct1[] ) {

	uint8_t byte[ 16 ];
	short i, j, counter = 0;
	
	for( i = 0; i < 4; ++i ) {
	
		for( j = 0; j < 4; ++j ) {
		
			//byte[ counter ] = (( state[ i ][ j ] << 4 ) & 0xf0 ) ^ ( state[ i ][ j + 1 ] & 0x0f );
			byte[i*4+j]  = state[i][j*2  ] << 4;
			byte[i*4+j] |= state[i][j*2+1];
		}
	}
	
	counter = 0;
	for( i = 32; i < 48; ++i ) {
	
		ct1[ i ] ^= byte[ counter ];
		++counter;
	}

	return;
}


void print_state( unsigned char state[8][8] ) {

	for( short i = 0; i < 8; ++i ) {
	
		for( short j = 0; j < 8; ++j ) 
			printf("%x ", state[ i ][ j ] );
		
		printf("\n");
	}
	
	printf("\n");

	return;
}

void printDDT( unsigned char **ptr ) {


	for( int i = 0; i < 16; ++i ) {

		for( int j = 0; j < 16; ++j ) {

			printf("%d ", ptr[ i ][ j ]);
		}
		printf("\n");
	}

	return;
}


unsigned char **diffDistribution(unsigned char s[sboxSize]) {

	int i; 
	int x, y, delta, delta1;
	
	unsigned char** count = malloc(sboxSize*sizeof(int *));
	
	for(i = 0; i < sboxSize; ++i) {
		
		count[i] = malloc(sboxSize*sizeof(int));
		memset(count[i],0,sboxSize*sizeof(int));
	}
		
	for(y = 0; y < sboxSize; ++y) {
		
		for(x = 0; x < sboxSize; ++x) {
			
			delta = y^x;
			delta1 = s[x]^s[y];
			count[delta][delta1]++;
		}		
	}
	
	return count;
}


void Recover_state_columnwise( unsigned char known_diff, unsigned char pos, unsigned char count, unsigned char **ptr ) {

	unsigned char nfst[ 8 ][ 8 ], fst[ 8 ][ 8 ], temp[ 8 ][ 8 ], col[ 8 ][ 8 ];
	FILE *f0, *f1, *f2, *f3, *f4, *f5, *f6, *f7;
	unsigned char diff[ 8 ], diff1[ 8 ], delta, filename[ 24 ];
	unsigned char i, j;
	time_t t;

	srand( (unsigned) time( &t ) );

	for (i = 0; i < 64; i++)
	{
		nfst[i / 8][i % 8] = (nfstate[i / 2] >> (4 * ((i & 1)^1))) & 0xf;
		fst[i / 8][i % 8] = (fstate[i / 2] >> (4 * ((i & 1)^1))) & 0xf;
	}
	
	for( i = 0; i < 8; ++i ) {
	
		for( j = 0; j < 8; ++j ) 
			temp[ i ][ j ] = nfst[ i ][ j ] ^ fst[ i ][ j ];
	}
	
	
	
	
	//print_state(nfst);
	//print_state(fst);
	
	//print_state(temp);
	printf("Full state difference::\n");
	for( short i = 0; i < 8; ++i ) {
	
		for( short j = 0; j < 8; ++j ) 
			printf("%x ", temp[ i ][ j ] );
		
		printf("\n");
	}
	
	printf("\n");
	
	invMixColumn( temp );
	//print_state( temp );
	invShiftRow( temp );
	//print_state( temp );
	
	printf("Full state difference::\n");
	for( short i = 0; i < 8; ++i ) {
	
		for( short j = 0; j < 8; ++j ) 
			printf("%x ", temp[ i ][ j ] );
		
		printf("\n");
	}
	
	printf("\n");
	
	printf("Right hand diff:\n");
	diff[ 0 ] = temp[ pos/8 ][ pos%8 ];
	
	printf("\n");
		
	sprintf(filename, "key_column%d,%d,%d,0.txt", pos/8,pos%8, count);
	if ((f0 = fopen(filename, "w")) == NULL) {
		fprintf(stderr, "Couldn't open <%s> for write\n", filename);
		exit(1);
	}
	for( i = 0; i < 16; ++i ) {
	
		
		//printf("0-> %x %x %x\n", i, s[ i ] ^ s[ i ^ diff1[ 0 ] ], diff[ 0 ]);
		if( ( s[ i ] ^ s[ i ^ known_diff ] ) == diff[ 0 ] ) {
			
			printf("f0:: i = %x, diff = %x\n", i, diff[ 0 ]);
			fprint_bstr(f0, "", &i, 1);
		}
		
	}
	
	fclose( f0 );
		
	return;
}


unsigned short findMax( unsigned short arr[] ) {

	unsigned short max = 0;

	for( unsigned char i = 0; i < 16; ++i ) {
	
		if( max < arr[ i ] )
			max = arr[ i ];
	}

	return( max );
}


void state_nibble( unsigned char pos, unsigned char value ) {

	FILE *fp1; 
	unsigned char val;
	unsigned short max, arr[ 16 ] = {0};
	unsigned short num = 0, count1 = 0;
	unsigned char filename[ 24 ];

	//int number = 8;
	//printf("State[%d]\n");
	
	printf("count = %d, ", value);
	for( unsigned char count = 0; count < value; ++count ) {
	
		sprintf(filename, "key_column%d,%d,%d,0.txt", pos/8,pos%8,count);
		if ((fp1 = fopen(filename, "r+")) == NULL) {
			fprintf(stderr, "Couldn't open <%s> for read\n", filename);
			exit(1);
		}
		fseek(fp1, 0, SEEK_SET);
		while(fread(&val, 1, 1, fp1) == 1) {
		

			//printf ("val = %c", val);
			if( ( val == 'a' ) || ( val == 'b' ) || ( val == 'c' ) || ( val == 'd' ) || ( val == 'e' ) || ( val == 'f' ) )
				val = val - 97 + 10;
			else 
				val = val - 48;
				
			//printf ("......val = %x\n", val);
			
			arr[ val ] += 1;
		}
		//printf("\n");
		fclose( fp1 );
	}
	printf("Recovered nibble value at (%d,%d)-th position of the state::\n", pos/8, pos%8);
	printf("{ ");

	max = findMax( arr );
	printf("max = %d:: ", max);
	for( unsigned char i = 0; i < 16; ++i ) {

		if( arr[ i ] == max ) {
		
			printf("%x ", i );
			//printf("1st column = %04x\n", i);
			//++count1;
		}
	}
	printf("}\n\n");
	
	return;
}


int generate_test_vectors()
{
	FILE                *fp;
	char                fileName[MAX_FILE_NAME];
	unsigned char       key[CRYPTO_KEYBYTES] = {0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0xf1};
	unsigned char		nonce[CRYPTO_NPUBBYTES] = {0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0xf1};
	unsigned char       msg[MAX_MESSAGE_LENGTH] = {0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0xf1};
	unsigned char       msg2[MAX_MESSAGE_LENGTH];
	unsigned char		ad[MAX_ASSOCIATED_DATA_LENGTH] = {0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0x10, 0x20, 0x30, 0xf1};
	unsigned char		ct[MAX_MESSAGE_LENGTH + CRYPTO_ABYTES], ct1[MAX_MESSAGE_LENGTH + CRYPTO_ABYTES];
	//unsigned long long  clen, mlen2;
	//int                 count = 1;
	int                 func_ret, ret_val = KAT_SUCCESS;
	
	unsigned long long mlen, mlen2, clen, adlen;
	unsigned char diff, diff1;
	uint8_t state[ 8 ][ 8 ], dstate[8][8];
	unsigned char tag[ 16 ];
	unsigned char count = 0, pos = 0;
	unsigned char **ddt = diffDistribution(s);
	int i, j, i1;
	
	
	time_t t;
	srand( (unsigned) time( &t ) );

	//init_buffer(key, sizeof(key));
	init_buffer(nonce, sizeof(nonce));
	init_buffer(msg, sizeof(msg));
	init_buffer(ad, sizeof(ad));
	
	mlen = adlen = mlen2 = 32;
	clen = 48;
	
	printDDT( &ddt[ 0 ] );
	
	printf("...............Encryption.....................\n");
	if ( crypto_aead_encrypt(ct, &clen, msg, mlen, ad, adlen, NULL, nonce, key) == 0)
		print(ct);
		
	for( i = 32; i < 48; ++i )
		tag[i-32] = ct[i];
		
	if ( crypto_aead_decrypt(msg2, &mlen2, NULL, ct, clen, ad, adlen, nonce, key) == 0) {
	
		print(ct);
		printf("Decryption is successful!!\n\n\n");
	}
	else
		printf("Not successful!!\n\n\n");
		
		
		
	count = 0;
	for( pos = 0; pos < 64; ++pos ) {
	
		diff = rand() & 0xf;
		if( diff == 0 )
			diff = rand() & 0xf;
	
		printf("faulty forgery by injecting fault at the nibble position (%d,%d)\n\n", pos/8, pos%8);	
		for( i1 = 0; i1 < 10000; ++i1 ) {
		
			for( i = 0; i < 8; ++i ) {

				for( j = 0; j < 8; ++j )
					state[ i ][ j ] = 0;
			}
			
			diff1 = rand() & 0xf;
			if( diff1 == 0 )
				diff1 = rand() & 0xf;
			state[ pos / 8 ][ pos % 8 ] = diff1;
			
			//printf("state difference before sr and mc:\n");
			//print_state( state );
			ShiftRow(state);
			MixColumn( state );
			//printf("state difference after sr and mc:\n");
			//print_state( state );
			copy_ciphertext( ct1, ct );
			xor_of_diff_tag( state, ct1 );
			
			printf("At %d-th query::\n", i1);
			//printf("fault in the dec query\n");	
			if ( fault_on_crypto_aead_decrypt(msg2, &mlen2, NULL, ct1, clen, ad, adlen, nonce, key, diff, pos ) == 0 ) {
				
				printf("\nTag Compare is successful!!Tag Compare is successful!!Tag Compare is successful!!Tag Compare is successful!! at position position = (%d, %d) with input diff = %x, output diff = %x\n\n", (pos/8), (pos%8),diff,diff1);

				//printf("enter into the fun::Recover_state_columnwise\n");
				Recover_state_columnwise( diff, pos, count, &ddt[ 0 ] );
				//return 0;
				++count;
				
				diff1 = rand() & 0xf;
				while(diff1 == diff )
					diff1 = rand() & 0xf;
				diff = diff1;
				
				
			}
			if(count == number)
				break;							
			}
			count = 0;
		}
			
	
	printf("faulty tag::\n");
	print(ct1);
	printf("Actual TAG DIFFERENCES:\n");
	for( i = 0; i < 16; ++i ) 
		printf("%x, ", ftag[i]^tag[i]);
		
	printf("\nActual state values before s-box\n");
	for( short i = 0; i < 8; ++i ) {
	
		for( short j = 0; j < 8; ++j ) {
		
			//dstate[i][j] = st[ i ][ j ]^st1[ i ][ j ];
			printf("%x ", st[ i ][ j ]);
		}
		
		printf("\n");
	}
	
	printf("\n");
	
		
	for( pos = 0; pos < 64; ++pos )
		state_nibble( pos, 2 );
	
	return 0;
}


void fprint_bstr(FILE *fp, const char *label, const unsigned char *data, unsigned long long length)
{    
    //fprintf(fp, "%s", label);
        
	for (unsigned long long i = 0; i < length; i++)
		fprintf(fp, "%x", data[i]);
	    
    //fprintf(fp, " ");
}

void init_buffer(unsigned char *buffer, unsigned long long numbytes)
{
	for (unsigned long long i = 0; i < numbytes; i++)
		buffer[i] = (unsigned char)i;
}
