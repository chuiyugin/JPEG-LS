//            ******************************************************************           
//            *                      JPEG_LS_decodeԴ�����嵥                  *
//            ******************************************************************

//     ************ 
//     *�������ļ�* 
//     ************ 
#include <iostream.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <sys\types.h>
#include <sys\timeb.h>
//     ************ 
//     *  �궨��  * 
//     ************ 
//RESET:  threshold value at which A,B,and N are halved
//NEAR:   difference bound for near-lossless coding
//MIN_C:  minimum allowed value of C[0..364],equal to -128
//MAX_C:  maximum allowed value of C[0..364],equal to 127
#define RESET 64
#define NEAR 0
#define MIN_C -128
#define MAX_C 127
#define MAXVAL 255

//     ************************************
//     *           ȫ�ֱ�����ʼ��         *    
//     ************************************ 
//MAXVAL:   maximum possible image sample value ove all component of a scan
//RUNindex: index for run mode order
//qbpp:     number of bits needed to represent a mapped error value
//bpp:      number of bits needed to represent MAXVAL,with a minimum of 2
//LIMIT:    the value of glimit for a sample encoded in regular mode
//Q:        context determined from Q1,Q2,Q3
//RANGE:    range of prediction error representation
//A[0..366]:367 counters for the accumulated preditection error magnitude
//B[0..364]:365 counters for computing the bias
//C[0..364]:365 counters storing prediction coreection values
//J[0..31]: 32 variables indicating order of run-length codes
//N[0..366]:367 counters for frequency of occurrence of each context
//Nn[365..366]:2 counters for negative prediction error for run interruption
//EOLine:   end of line indicator,used in run mode 
//Errval:   prediction error
//EMErrval: Errval mapped to non-negative integers in run interruption mode
//MErrval:  Errval mapped to non-negative integers in regular mode
//--------------------------------------------------------------------------------
//    LinX:��ǰ�к�
//    RowX:��ǰ�к�
//    *f:ָ��������ָ��
//    *fp:�ļ�ָ��   
//    buffer:��ֵ������
//    output:�������ֵ
//    size:��ǰ�����ĳ���
//    decode:��ǰ��������ֵ
//    decode2:��ʱ����
//    flag1:��־λ
      
    unsigned long buffer=0,output=0,decode=0,decode2=0;
	int size=0;
	int LinX=1,RowX=1; 
    int RANGE;
	static int RUNindex=0; 
	int *f;
	int flag1=0,bpp;
	int B[365],C[365];
	int LIMIT;
	int J[32]={0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,5,5,6,6,7,7,8,9,10,11,12,13,14,15};
	int A[367],N[367];
	int Nn[2]={0};
	int EOLine=0;
	FILE *fp;

//     **********************************
//     *      ����T1,T2,T3ֵ���ӳ���    *
//     **********************************	
  float CLAMP_1(float i)
{
	if(i>MAXVAL||i<NEAR+1)
		return(NEAR+1);
	else
		return(i);
}
 float CLAMP_2(float i,float T1)
{
	if(i>MAXVAL||i<T1)
		return(T1);
	else
		return(i);
}
float CLAMP_3(float i,float T2)
{
	if(i>MAXVAL||i<T2)
		return(T2);
	else
		return(i);
}	
//     ******************************	
//     *  ����������ĳ��ȵ��ӳ���  *
//     ******************************
  int LG(int Q)
		{
	     int i;		
	     for(i=0;(N[Q]<<i)<A[Q];i++);
	     return(i);
		}
	
//       ****************************************     
//       *        ���������̵��ӳ���          *
//       ****************************************  	


 void  RegularModeProcessing(int qbpp,int Ra,int Rb,int Rc,int Rd,int D1,int D2,int D3,int y,float T1,float T2,float T3)
	{
//       ********************
//       *  �����ݶȵ�����  *
//       ********************
		int Di[4]={0,D1,D2,D3};
		int Qi[4],Q;
		int SIGN,k,q,decode1,Rx,i;
		int Px,Errval,MErrval;
        int cnt=0;
		output=0;	
		for(i=1;i<4;i++)
		{
			if(Di[i]<=-T3)      Qi[i]=-4;
			else if(Di[i]<=-T2) Qi[i]=-3;
			else if(Di[i]<=-T1) Qi[i]=-2;
			else if(Di[i]<(-NEAR)) Qi[i]=-1;
			else if(Di[i]<=NEAR) Qi[i]=0;
			else if(Di[i]<T1) Qi[i]=1;
			else if(Di[i]<T2) Qi[i]=2;
			else if(Di[i]<T3) Qi[i]=3;
			else Qi[i]=4;
		}
//         ********************************************** 
//         *  ��ɴ�ʸ����Q1,Q2,Q3)��Q��һһ��Ӧ��ӳ��  *
//         **********************************************		    
		    if((Qi[1]<0)||((Qi[1]==0)&&(Qi[2]<0))||(((Qi[1]==0)&&(Qi[2]==0))&&(Qi[3]<0)))
				     SIGN=-1;
			else     SIGN=1;
			if(SIGN==-1)
			{  
				for(i=1;i<4;i++)
			        Qi[i]=Qi[i]*SIGN;
			}
			Q=(Qi[1]*9+Qi[2])*9+Qi[3];
		    
//          ********************* 			 
//          *    ����Px��ֵ     *
//          *********************
	/*	if(Rc>=__max(Ra,Rb)){
		Px=__min(Ra,Rb);
	c=1;
	if(Rc-__max(Ra,Rb)>=10)
				Px--;	}
	else{
		if(Rc<=__min(Ra,Rb)){
			Px=__max(Ra,Rb);
			c=1;
		 if(__min(Ra,Rb)-Rc>=10)
				Px++;}
		else{
			Px=Ra+Rb-Rc;
		c=0;}
	}
	if(c==0)
	Px=(Px+Ra+Rb)/3;*/
	/*if(Rc<=__max(Ra,Rb)){
				if(Rc<=__min(Ra,Rb)){
					if((10<=(Rd-Rb))&&(abs(Ra-Rb))<=10&&(__min(Ra,Rb)-Rc)>=5&&(Rd-Rb)<=50)
						Px=Rd/2+__max(Ra,Rb)/2;
					else 
						Px=__max(Ra,Rb);}
				else
					Px=Ra+Rb-Rc;}
			else{
				if(Rc-Ra>=10&&Rd<Rb&&Ra-Rb<=5)
					Px=Rd/2+__min(Ra,Rb)/2;
				else 
					Px=__min(Ra,Rb);
			}*/

	if(Rc>=__max(Ra,Rb))
		Px=__min(Ra,Rb);
	else{
		if(Rc<=__min(Ra,Rb))
			Px=__max(Ra,Rb);
		else
			Px=Ra+Rb-Rc;
	}
	if(SIGN==1)
		Px=Px+C[Q];
	else
		Px=Px-C[Q];
//       **********************************	
//       *  ��Px��������0..MAXVAL)�ķ�Χ  *
//       **********************************
	if(Px>MAXVAL)
		Px=MAXVAL;
	else if(Px<0)
		Px=0;
//      ******************************************************
//      *            �������лָ��ؽ�ֵRx                    *
//      ******************************************************	
     k=LG(Q);

	if(decode!=0)/*֮ǰΪ�γ̽��룬��һ����Ԫδ�����ת�볣�����ʱ������ʣ�µĲ���*/
	{
		while(((1<<(size-1))&decode)==0)/*��һԪ��*/
		{
		  size--;
          cnt++;
		}
		size--;
	  if(size==0)
		decode=0;
	  else
	    decode=(decode<<(32-size))>>(32-size);
	}
	else{ 
		while(decode==0)
		{
		 fread(&buffer,1,1,fp);
		 decode=buffer;
		 size=size+8;/*��8bitΪ��λ����*/
	     cnt=size;	   
		}
		   q=7;/*Ԥ��߼�λ�γɵ�q��7(�Ǵ���Ԫ�ܴﵽ�����ֵ)*/
		   while(((1<<q)&decode)==0)
			   q--;
           cnt=cnt-8+7-q;/*0�ĸ���*/ 		
           if(q==0)
			   decode=0;
		   else
		       decode=(decode<<(32-q))>>(32-q);/*�����kλ��֮ǰ����*/
		   size=q;
	}

		   if(cnt<(LIMIT-qbpp-1))/*���1*/
		   {
                  if(k<=size)
				  {
                   output=decode>>(size-k);/*�õ���kλ*/
				     if(size-k==0)
					   decode=0;
				     else
				       decode=((decode<<(32-size+k)))>>(32-size+k);/*�˴δ������������*/
                       size=size-k;		   
				  }

		         else
				 {
			      fread(&buffer,1,1,fp);
			      decode1=0;
			      if(k-size<=8)
				  decode1=decode<<(k-size);
			      while(k-size>8)
				  {
				   decode1=decode1+(decode<<(k-size))+(buffer<<(k-size-8));
                   k=k-8;
				   fread(&buffer,1,1,fp);
				   decode=0;
				  }
			   output=decode1+(buffer>>(8+size-k));/*�ڶ����ʾ��k<size�ĵ�Ԫ��õ���ǰ��kλ��*/
			   if(8-k+size==0)
				   decode=0;
			   else
			       decode=(buffer<<(32-8+k-size))>>(32-8+k-size);/*�������������*/
			   size=8-k+size;
				 }
		   MErrval=(cnt<<k)+output;
		   }
           else/*���2*/
		   { 
			   if(qbpp<=size)
				  {
                  output=decode>>(size-qbpp);
		          if(size==qbpp)
					  decode=0;
				  else
				    decode=((decode<<(32-size+qbpp)))>>(32-size+qbpp);
			       size=size-qbpp;    
			   }

				else
				{
			   fread(&buffer,1,1,fp);
			    decode1=0;
	           	if(qbpp-size<=8)
					decode1=decode<<(qbpp-size);
			   while(qbpp-size>8)
			   {
				   decode1=decode1+(decode<<(qbpp-size))+(buffer<<(qbpp-size-8));
                   qbpp=qbpp-8;
				   fread(&buffer,1,1,fp);
				   decode=0;
			   }
			   output=decode1+(buffer>>(8+size-qbpp));
			   if(8-qbpp+size==0)
				   decode=0;
			   else
			       decode=(buffer<<(32-8+qbpp-size))>>(32-8+qbpp-size);
			   size=8-qbpp+size;
				}
		   MErrval=output+1;
        }             

		 if((NEAR==0)&&(k==0)&&(2*B[Q]<=-N[Q]))
{
	if((MErrval&1)==1)
		Errval=(MErrval-1)>>1;
	else
		Errval=(-(MErrval>>1))-1;
}
else
{
	if((MErrval&1)==0)
		Errval=((MErrval)>>1);
	else
		Errval=-((MErrval+1)>>1);
}
//      *********************************		
//      *        ���¸�������           *
//      *********************************	

B[Q]=B[Q]+Errval*(2*NEAR+1);
A[Q]=A[Q]+abs(Errval);
if(N[Q]==RESET)
{
	A[Q]=A[Q]>>1;
	B[Q]=B[Q]>>1;
	N[Q]=N[Q]>>1;
}
N[Q]=N[Q]+1;
Errval=Errval*(2*NEAR+1);
if(SIGN==-1)
  Errval=-Errval;
  Rx=Errval+Px;
if(Rx<(-NEAR))
   Rx=Rx+RANGE*(2*NEAR+1);
else if(Rx>(MAXVAL+NEAR))
   Rx=Rx-RANGE*(2*NEAR+1);
if(Rx<0)
Rx=0;
else if(Rx>MAXVAL)
Rx=MAXVAL;  
*(f+LinX*(y+2)+RowX)=Rx;

if(B[Q]<=-N[Q])
{
		B[Q]=B[Q]+N[Q];
		if(C[Q]>MIN_C)
			C[Q]=C[Q]-1;
		if(B[Q]<=-N[Q])
			B[Q]=-N[Q]+1;
}
		else if(B[Q]>0)
		{
			B[Q]=B[Q]-N[Q];
			if(C[Q]<MAX_C)
				C[Q]=C[Q]+1;
			if(B[Q]>0)
				B[Q]=0;
	
		}
}
//              **********************************
//              *      �γ̽����ӳ���Ķ���      *
//              **********************************
void  RunModeProcessing(int qbpp,int Ra,int Rb,int y)
 {
	 int decode1=0;
	 int cnt=0,i;
	 unsigned long j;
	 int RItype,TEMP,AQ,Errval,EMErrval,flag,map,SIGN,k,Px,Rx,Q;
//            **********************************
//            *    �������лָ�EMErrval        *
//            **********************************	 
	 if(size==0){   
	     fread(&buffer,1,1,fp);
		 decode=buffer;
   	     size=8;}/*��8bitΪһ������λ*/
         size--;
	 while((1&(decode>>size))==1)
		 {
			 size--;		     
			 i=0;
			 while(i<(1<<J[RUNindex]))/*дһ��Ra*/
			 {
				 *(f+LinX*(y+2)+RowX)=Ra;
               
 				 RowX++;
				 if(RowX>y)
				 {
                     RowX--;
					 flag1=1;
				}
				 i++; 
				 if(flag1==1)
					 break;
       		 }
			 if((i==(1<<J[RUNindex]))&&RUNindex<31)
				 RUNindex++;
			 if(size<0&&flag1==0)
				 {
					 fread(&buffer,1,1,fp);
					 decode=buffer;
   				     size=7;
				 }/*һ����Ԫ���������γ���δ������������һ����Ԫ*/
			if(flag1==1)
				break;
				 
		 }
					/***���Ѵ����λ������***/
		         if(RowX==y&&flag1==1){/*���1������ĩ*/
                 if(size==-1)/*���ô�����һ����Ԫ���γ�δ����*/
					 decode=0;/*���������㣬����γ̽���*/
				 else/*�Ե�Ԫδ��������ѵ���ĩ*/
				 decode=(decode<<(32-size-1))>>(32-size-1);/*������ĩ�ж�ʱ����ʣ�µ�rkλ1ǰ׺��1������Ҳ��ǰ��Ĵ����size��1��δ����ģ�����32��size��1��ʾ�ڵ�ǰ����Χ���Ѵ���ġ��˲�����ʾ���Ѵ����λ����*/
				 size=size+1;/*�������λ����size��1*/
                 flag1=0;
				 return;}/*�γ̽������*/
         if(size==0)/*���2������ĩ������һ����Ԫ�����һ���ǲ�ͬ����*/
				decode2=0;
         else      
			   decode2=(decode<<(32-size))>>(32-size);/*ʣ��size��Ԫ�ش�����*/
					/***�Գ���С��rm�ķֶ����ֵĴ���***/
		   if(J[RUNindex]<=size)/*����ʣ����س���ʱ�����ڵ�ǰ����Ԫ��*/
		   {
           output=(decode2>>(size-J[RUNindex]));/*��������������������Ҳ࣬���õ������������*/
		   if(J[RUNindex]==size)
			   decode=0;
		   else
		   decode=((decode<<(32-size+J[RUNindex]))>>(32-size+J[RUNindex]));/*���������λ����*/
		   size=size-J[RUNindex];
		   }
		   else/*��ǰ����Ԫʣ��ı���С��rkʱ*/
		   {
			   fread(&buffer,1,1,fp);
			   
			   if(J[RUNindex]-size<=8)/*rk����һ������Ԫ֮��*/
				   decode1=decode2<<(J[RUNindex]-size);/*������һ����Ԫ��ʣ�²��ֵĿռ�*/
			   while(J[RUNindex]-size>8)
			   {
				   decode1=decode1+(decode2<<(J[RUNindex]-size))+(buffer<<(J[RUNindex]-size-8));/*������漸����Ԫ��rk����.ע������ļӲ�����ʾ������ӣ�������ͬһԭ���ϵ���*/
                   J[RUNindex]=J[RUNindex]-8;
				   fread(&buffer,1,1,fp);
				   decode2=0;
			   }
			   output=decode1+(buffer>>(8+size-J[RUNindex]));/*�ұߵڶ����ǵ�rk��size<8ʱ���õ���ǰ��Ԫ��ʣ���rk���Խӵ�n������Ԫ֮��*/
			   if(J[RUNindex]-size==8)
				   decode=0;
			   else
			       decode=(buffer<<(32-8+J[RUNindex]-size))>>(32-8+J[RUNindex]-size);/*��ǰ���Ѿ�������ģ�n������Ԫ����ǰ��Ԫʣ��rk��λ����*/
			       size=8-J[RUNindex]+size;
		   }
		   if(RUNindex>0)
			   RUNindex--;
		   for(j=0;j<output;j++){
			   *(f+LinX*(y+2)+RowX)=Ra;
			   RowX++;}
              if(RowX>y){
				   RowX=RowX-y;
				   LinX++;
			   }
		  	  
		  if(decode!=0){
			   while(((1<<(size-1))&decode)==0){
				   size--;
                   cnt++;
			   }
			   size--;
			   if(size==0)
				   decode=0;
			   else
			       decode=(decode<<(32-size))>>(32-size);
		   }
		   else{ 
			       while(decode==0)
				   {
			       fread(&buffer,1,1,fp);
			       decode=buffer;
				   size=size+8;
	               cnt=size;	   
				   }
		   int q=7;
		   while(((1<<q)&decode)==0)
			   q--;
           cnt=cnt-8+7-q; 		
           if(q==0)
			   decode=0;
		   else
		        decode=(decode<<(32-q))>>(32-q);		
           size=q;
			  }
         Rb=*(f+(LinX-1)*(y+2)+RowX);
		 if(abs(Ra-Rb)<=NEAR)
			 RItype=1;
		 else
			 RItype=0;
		 if(RItype==1)
			 Px=Ra;
		 else
			 Px=Rb;
		 if((RItype==0)&&(Ra>Rb))
		 {
			 SIGN=-1;
		 }
		 else
			 SIGN=1;
		 if(RItype==0)
			 TEMP=A[365];
		 else
			 TEMP=A[366]+(N[366]>>1);
		  Q=RItype+365;
		  AQ=A[Q];
		   A[Q]=TEMP;
		   k=LG(Q);
		 
		   if(cnt<(LIMIT-J[RUNindex]-qbpp-2))
		   {
                  if(k<=size)
				  {
                   output=decode>>(size-k);
		           if(size==k)
					   decode=0;
				   else
				       decode=((decode<<(32-size+k)))>>(32-size+k);
                   size=size-k;		   
				  }

		          else
				  {
			       fread(&buffer,1,1,fp);
			       decode1=0;
			       if(k-size<=8)
				   decode1=decode<<(k-size);
			       while(k-size>8)
				   {
				   decode1=decode1+(decode<<(k-size))+(buffer<<(k-size-8));
                   k=k-8;
				   fread(&buffer,1,1,fp);
				   decode=0;
				   }
			       output=decode1+(buffer>>(8+size-k));
			       if(8-k+size==0)
					   decode=0;
				   else
				       decode=(buffer<<(32-8+k-size))>>(32-8+k-size);
			       size=8-k+size;
				  } 
		           EMErrval=(cnt<<k)+output;
		   }
              else
			  { 
			   if(qbpp<=size)
				  {
                 output=decode>>(size-qbpp);
                 if(size-qbpp==0)
					 decode=0;
				 else
		          decode=((decode<<(32-size+qbpp)))>>(32-size+qbpp);
				 size=size-qbpp;
			   }
		   else
		   {
			   fread(&buffer,1,1,fp);
			   decode1=0;
	           	if(qbpp-size<=8)
					decode1=decode<<(qbpp-size);
			   while(qbpp-size>8)
			   {
				   decode1=decode1+(decode<<(qbpp-size))+(buffer<<(qbpp-size-8));
                   qbpp=qbpp-8;
				   fread(&buffer,1,1,fp);
				   decode=0;
			   }
			   output=decode1+(buffer>>(8+size-qbpp));
			  if(8-qbpp+size==0)
				  decode=0;
			  else
			      decode=(buffer<<(32-8+qbpp-size))>>(32-8+qbpp-size);
			   size=8-qbpp+size;
		   }
		   EMErrval=output+1;
        }             
//         **************************************         
//	       *      ��EMErrval���Errval          *
//         **************************************			  
	     if(((EMErrval&1)==0)&&(RItype==1))
			 map=1;
		 else if(((EMErrval&1)==1)&&(RItype==1))
			 map=0;
		 else if(((EMErrval&1)==1)&&(RItype==0))
			 map=1;
		 else if(((EMErrval&1)==0)&&(RItype==0))
			 map=0;
	
		 if((map==0&&k!=0)||(map==0&&k==0&&2*Nn[Q-365]>=N[Q])||(map==1&&k==0&&2*Nn[Q-365]<N[Q]))
             Errval=(EMErrval+RItype+map)>>1;
		 else
             Errval=-((EMErrval+RItype+map)>>1); 
		 flag=Errval;

		 Errval=Errval*(2*NEAR+1);
		 if(SIGN==-1)
			 Errval=-Errval;
			 
		 Rx=Errval+Px;
		 
		 if(Rx<(-NEAR))
			 Rx=Rx+RANGE*(2*NEAR+1);
		 if(Rx>(MAXVAL+NEAR))
			 Rx=Rx-RANGE*(2*NEAR+1);
		 if(Rx<0)
			 Rx=0;
		 else if(Rx>MAXVAL)
			 Rx=MAXVAL;
		 *(f+LinX*(y+2)+RowX)=Rx;
//       **********************************
//       *           ���������           *
//       **********************************         
		 if(flag<0)
			 Nn[Q-365]=Nn[Q-365]+1;
             A[Q]=AQ;
             A[Q]=A[Q]+((EMErrval+1-RItype)>>1);
         if(N[Q]==RESET)
		 {
	     A[Q]=A[Q]>>1;
	     N[Q]=N[Q]>>1;
		 Nn[Q-365]=Nn[Q-365]>>1;
		 }
          N[Q]=N[Q]+1;
    
 }         
//                  *************************************************
//                  *                    ������                     *
//                  *************************************************

//     i,j:ѭ������������
//	   _______________________
//     |   | Rc| Rb| Rd|   |
//     -----------------------           
//	   |   | Ra| Ix|   |   |
//	   -----------------------	
//     D1,D2,D3:��ǰ�ݶ�
//     x,y:ͼ��ĳ��ȺͿ��

 	void main()
{
    int x,y,i,j;
	int Ra,Rb,Rc,Rd,D1,D2,D3;
	int BASIC_T1=3,BASIC_T2=7,BASIC_T3=21;
	float T1,T2,T3;
 	int qbpp,filemode;
	struct timeb start_time,end_time;
	int second_d;
	//printf("ͼ���Ⱥ͸߶�\n");
	//scanf("%d,%d",&x,&y);
	x=y=128;
    //printf("ѡ���ļ���ʽ(0:Adata5.dat,1:Adata5.raw)\n");
    //scanf("%d",&filemode);
	filemode=1;
    ftime(&start_time);
//            *********************************
//            *       �����������ֵ          *
//            *********************************	
	RANGE=((int)((MAXVAL+2*NEAR)/(2*NEAR+1)))+1;
    qbpp=-(int)(floor(-log(RANGE)/log(2.0)));
	bpp=__max(2,-(int)(floor(-log(MAXVAL+1)/log(2.0))));
    LIMIT=2*(bpp+__max(8,bpp));
     if(MAXVAL>=128){
		T1=CLAMP_1((float)((int)(__min(MAXVAL,4095)+128)/256)*(BASIC_T1-2)+2+3*NEAR);
        T2=CLAMP_2((float)((int)(__min(MAXVAL,4095)+128)/256)*(BASIC_T2-3)+3+5*NEAR,T1);
        T3=CLAMP_3((float)((int)(__min(MAXVAL,4095)+128)/256)*(BASIC_T3-4)+4+7*NEAR,T2);}
		else{
			T1=CLAMP_1((float)__max(2,BASIC_T1/(int)(256/(MAXVAL+1))+3*NEAR));
			T2=CLAMP_2((float)__max(3,BASIC_T2/(int)(256/(MAXVAL+1))+5*NEAR),T1);
            T3=CLAMP_3((float)__max(4,BASIC_T3/(int)(256/(MAXVAL+1))+7*NEAR),T2);
		}

	f=(int *)calloc((x+1)*(y+2),sizeof(int));	  
		
	if((fp=fopen("E:\\felicia\\Adata2","rb"))==NULL)
		{
			printf("cannot open the file\n");
				return;
		}
		

//       ******************************		
//       *     �Ը�����ĳ�ʼ��       *
//       ******************************
	for(j=0;j<365;j++)
	{
		A[j]=__max(2,(RANGE+(1<<5))/(1<<6));         
		N[j]=1;
		B[j]=0;
		C[j]=0;
	}
	A[365]=A[0];
	A[366]=A[0];
	N[365]=1;
	N[366]=1;
//    ************************	
//    *      �������        *
//    ************************
 	for(i=0;i<(x+1)*(y+2);i++)
		*(f+i)=0;
	
   while(RowX<=y&&LinX<=x)
	{ 
	Ra=(*(f+LinX*(y+2)+RowX-1));
	Rb=(*(f+(LinX-1)*(y+2)+RowX));
    Rc=(*(f+(LinX-1)*(y+2)+RowX-1));
	Rd=(*(f+(LinX-1)*(y+2)+RowX+1));
	D1=Rd-Rb;
	D2=Rb-Rc;
	D3=Rc-Ra;
	
//   ******************************    
//   *       ѡ����뷽ʽ         *
//   ******************************	
	if((abs(D1)<=NEAR)&&(abs(D2)<=NEAR)&&(abs(D3)<=NEAR))
		RunModeProcessing(qbpp,Ra,Rb,y);
    else
		RegularModeProcessing(qbpp,Ra,Rb,Rc,Rd,D1,D2,D3,y,T1,T2,T3);
	if(RowX==y){
		  *(f+LinX*(y+2)+y+1)=*(f+LinX*(y+2)+y);
          *(f+(LinX+1)*(y+2))=*(f+LinX*(y+2)+1);}
	      
	RowX++;
   	if(RowX>y)
		{
		RowX=RowX-y;
		LinX++;
		}
}
  // printf("max_k=%d\n",max_k);
    fclose(fp);
//          *************************************
//          *         �ļ������ʽѡ��          *
//          *************************************	
 if(filemode==0)
   {
        if((fp=fopen("E:\\felicia\\Adata5.dat","wt"))==NULL)
		{
			printf("cannot open the file\n");
			exit(0);
		}
        for(i=1;i<x+1;i++)
		{  
		   for(j=1;j<y+1;j++)
              fprintf(fp,"%5d",*(f+i*(y+2)+j));
           fprintf(fp,"\n");
		}
   }
   else
   {
         if((fp=fopen("E:\\felicia\\Adata5.raw","wb"))==NULL)
		  {
			printf("cannot open the file\n");
			exit(0);
		  }
	      for(i=1;i<x+1;i++)
		    for(j=1;j<y+1;j++)
               fprintf(fp,"%c",(unsigned char)*(f+i*(y+2)+j));
               //fwrite((f+i*(y+2)+j),2,1,fp);	
   }
 	fclose(fp);
//     **************************
//     *      �������ʱ��      *
//     **************************		
	ftime(&end_time);
	second_d=end_time.millitm-start_time.millitm;
	second_d=second_d+(end_time.time-start_time.time)*1000;
	printf("The encoding costs:%.3f seconds.\n",(float)second_d/1000.0);
	
	}



