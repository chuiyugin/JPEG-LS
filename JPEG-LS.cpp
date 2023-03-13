//            ******************************************************************           
//            *                      JPEG-LS源程序清单                         *
//            ******************************************************************

//     ************ 
//     *包含库文件* 
//     ************ 

#include <iostream.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <sys\types.h>
#include <sys\timeb.h>
//     ************ 
//     *  宏定义  * 
//     ************ 
//RESET:  threshold value at which A,B,and N are halved
//NEAR:   difference bound for near-lossless coding
//MIN_C:  minimum allowed value of C[0..364],equal to -128
//MAX_C:  maximum allowed value of C[0..364],equal to 127
#define RESET 64
#define NEAR 0
#define MIN_C -128
#define MAX_C 127

//     ************************************
//     *           全局变量初始化         *    
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
//    LinX:当前行号
//    RowX:当前列号
//    *f:指向码流的指针
//    *fp:文件指针   
//    counter:计算编码文件长度
//    output:编码的数值
//    cnt:当前码流的长度
//    code:当前码流的数值
//    pp:前一码流的长度    
    int MAXVAL=0; 
    unsigned long  output=0;//输出码流
    static int cnt=0,code=0,pp=0;//计数器
	int LinX=1,RowX=1; //当前点的行列值
	static int RUNindex=0; 
	int qbpp,bpp,*f;
	static int B[365],C[365];
	int LIMIT,Q,RANGE;
	int J[32]={0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,5,5,6,6,7,7,8,9,10,11,12,13,14,15};
	int A[367],N[367];
	int Nn[2]={0};
	int EOLine=0;
	long int counter=0;
	FILE *fp;
//     **********************************
//     *      计算T1,T2,T3值的子程序    *
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
//     *  求算术编码的长度的子程序  *
//     ******************************
  int LG(int Q)
		{
	     int i;		
	     for(i=0;(N[Q]<<i)<A[Q];i++);
	     return(i);
		}
//      ******************************
//      *      规整Errval的值        *
//      ****************************** 
  int ModRange(int a)
  {
	  if(a<((0-RANGE)/2))
		 a=a+RANGE;
	  if(a>=((1+RANGE)/2))
		  a=a-RANGE;
	  return(a);
  }
//        **************************************
//        *         写码流的子程序             *
//        **************************************
  void writecode(int *cnt,int *pp,unsigned long *output,int *code)
  {
	  unsigned long c;
	  if((*cnt)<8)
				*code=(*code<<(*cnt-*pp))+(*output);/*以1byte为单位处理。把之前的码流向前推当前码流的长度，加入当前输出的码流*/
	  else{
			while(*cnt>=8)
			{
				if(*cnt>32)/*以4byte为存储器最大值*/
					{
			   
			
					*code=(*code<<(8-*pp));
					fwrite(code,1,1,fp);/*把code指向的1×1个字节输出到fp所指的文件中*/
					counter++;
					*code=0;
					*cnt=*cnt-8;
					
					} 
				else        
					{
					*code=(*code<<(8-*pp))+(255&(*output>>(*cnt-8)));
					fwrite(code,1,1,fp);
					counter++;
					*code=0;
					*cnt=*cnt-8;
					}
			}
            c=~(~0<<*cnt);
			*code=c&(*output);
		}
  }
//          ****************************************     
//          *        常规编码过程的子程序          *
//          ****************************************  
  void  RegularModeProcessing(int y,int Ra,int Rb,int Rc,int Rd,int Ix,int D1,int D2,int D3,float T1,float T2,float T3)
	{
//       ********************
//       *  当地梯度的量化  *
//       ********************
		int Di[4]={0,D1,D2,D3};
		int Qi[4],Errval,MErrval;
		int i,k,SIGN,Rx,Px;
        unsigned interim;
		output=0;
		
	
			for(i=1;i<4;i++)
		{
			if(Di[i]<=-T3)      Qi[i]=-4;
			else if(Di[i]<=-T2) Qi[i]=-3;
			else if(Di[i]<=-T1) Qi[i]=-2;
			else if(Di[i]<-NEAR)Qi[i]=-1;
			else if(Di[i]<=NEAR)Qi[i]=0;
			else if(Di[i]<T1)   Qi[i]=1;
			else if(Di[i]<T2)   Qi[i]=2;
			else if(Di[i]<T3)   Qi[i]=3;
			else Qi[i]=4;
		}
//         ********************************************** 
//         *  完成从矢量（Q1,Q2,Q3)到Q的一一对应的映射  *
//         **********************************************
		    if((Qi[1]<0)||((Qi[1]==0)&&(Qi[2]<0))||(((Qi[1]==0)&&(Qi[2]==0))&&(Qi[3]<0)))
			SIGN=-1;
			else     SIGN=1;
			if(SIGN==-1)
			{  
				for(i=1;i<4;i++)
			        Qi[i]=Qi[i]*SIGN;
			}
			Q=(Qi[1]*9+Qi[2])*9+Qi[3];/*人为设定*/
//          ***************************** 			 
//          *    计算Px的值（预测）     *
//          *****************************			
	if(Rc>=__max(Ra,Rb))
		Px=__min(Ra,Rb);
	else{
		if(Rc<=__min(Ra,Rb))
			Px=__max(Ra,Rb);
		else
			Px=Ra+Rb-Rc;
	}/*边缘检测*/
/*		if(Rc<=__max(Ra,Rb)){
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
			}	*/	
	if(SIGN==1)
		Px=Px+C[Q];
	else
		Px=Px-C[Q];
//       **********************************	
//       *  将Px规整到（0..MAXVAL)的范围  *
//       **********************************
	if(Px>MAXVAL)
		Px=MAXVAL;
	else if(Px<0) 
		Px=0;/*预测修正*/
//       ******************** 	
//       *    计算Errval    *
//       ********************
   	Errval=Ix-Px;

	if(SIGN==-1)
		Errval=-Errval;

	if(Errval>0)
		Errval=(Errval+NEAR)/(2*NEAR+1);
	else
		Errval=-(NEAR-Errval)/(2*NEAR+1);/*量化预测误差*/
	Rx=Px+SIGN*Errval*(2*NEAR+1);/*重建*/
	
	if(Rx<0)
		Rx=0;
	else if(Rx>MAXVAL)
		Rx=MAXVAL;
    *(f+LinX*(y+2)+RowX)=Rx;/*用重建值代替实际值*/
//        ******************************************************	
//        *   将Errval规整到[-(RANGE-1)/2..+RANGE/2)的范围     *
//        ******************************************************
	Errval=ModRange(Errval);
//        ***********************************	
//        *    将Errval映射到MErrval        *
//        *********************************** 
	k=LG(Q);
	if((NEAR==0)&&(k==0)&&(2*B[Q]<=-N[Q]))
	{
		if(Errval>=0)
			MErrval=2*Errval+1;
		else
			MErrval=-2*(Errval+1);
	}
	else{
		if(Errval>=0)
			MErrval=2*Errval;
		else
			MErrval=-2*Errval-1;
	}
//        **********************************	
//        *      对MErrval进行编码         *
//        **********************************
	    interim=MErrval;
		interim=interim>>k;/*除最低k位以外的高位*/
		if(interim<((unsigned)(LIMIT-qbpp-1)))
		{
			unsigned b,c;
 			c=~(~0<<k);
			b=c&MErrval;/*截取MErrval的最低k位*/
			output=(output<<(interim+1))+1;/*左移interim＋1得到interim＋1个零，加一后即interim个零接一个1*/
   			output=output<<k;
			output=output+b;
//         *******************************   
//         *     向二进制文件写码流      *
//         *******************************			
		    pp=cnt;
			cnt=cnt+interim+1+k; 		
            writecode(&cnt,&pp,&output,&code);
			
		}
		else
		{
			unsigned b,c;
			output=(output<<(LIMIT-qbpp))+1;/*当前码流为：LIMIT-qbpp－1个零，一个1*/
			output=output<<qbpp;/*后接qbpp位的数字*/
			c=~(~0<<qbpp);
			b=c&(MErrval-1);/*取MErrval－1的后qbpp位*/
			output=output+b;
	        pp=cnt;
			cnt=cnt+LIMIT; 		
            writecode(&cnt,&pp,&output,&code);

		}
//      *********************************		
//      *        更新各个变量           *
//      *********************************		
		B[Q]=B[Q]+Errval*(2*NEAR+1);
		A[Q]=A[Q]+abs(Errval);
		if(N[Q]==RESET)
		{
			A[Q]=A[Q]>>1;
			B[Q]=B[Q]>>1;
			N[Q]=N[Q]>>1;
		}
		N[Q]=N[Q]+1;/*N[Q]指此种上下文出现的次数，最多为64次*/
//		Nt[Q]=Nt[Q]+1;
		if(B[Q]<=-N[Q]){
			B[Q]=B[Q]+N[Q];
			if(C[Q]>MIN_C)
				C[Q]=C[Q]-1;
			if(B[Q]<=-N[Q])
				B[Q]=-N[Q]+1;
		}
		else if(B[Q]>0){
			B[Q]=B[Q]-N[Q];
			if(C[Q]<MAX_C)
				C[Q]=C[Q]+1;
			if(B[Q]>0)
				B[Q]=0;
		}
				}
//              **********************************
//              *      游程编码子程序的定义      *
//              **********************************
    void RunModeProcessing(int x,int y,int Ra,int Rb,int Rc,int Rd,int Ix)
	{
        int cnt1=0;
		int RUNval=Ra;
		int RUNcnt=0,TEMP,RItype;
		int map,AQ,EMErrval,glimit,Errval,k,SIGN,Rx,Px;
        unsigned interim; 
        output=0;
//      ********************
//      *   计算游程长度   *
//      ********************		
		while(abs(Ix-RUNval)<=NEAR)
		{
			RUNcnt=RUNcnt+1;
			Rx=RUNval;
		   	*(f+LinX*(y+2)+RowX)=Rx;
			if(EOLine==1)/*正好是最后一个，跳到长度编码*/
			   break;
			else{
			 RowX=RowX+1;
           if(RowX==y){
			*(f+(LinX+1)*(y+2))=*(f+LinX*(y+2)+1);
			*(f+LinX*(y+2)+y+1)=*(f+LinX*(y+2)+y);/*当前象素为本行最后一个时，对其Rd、下一行Ra赋值*/
	        EOLine=1;}
    Rb=*(f+(LinX-1)*(y+2)+RowX);
	Ix=*(f+LinX*(y+2)+RowX);
			}
		}
//      ***************************************************
//      *   对游程长度进行编码并向二进制文件中写入码流    *
//      ***************************************************
		
		while(RUNcnt>=(1<<J[RUNindex]))
		{			
			output=(output<<1)+1;
			cnt1++;
            RUNcnt=RUNcnt-(1<<J[RUNindex]);
            if(RUNindex<31)
				RUNindex=RUNindex+1;
		}/*当RUNlen小于整数值的rm时，跳出*/
		if(EOLine==0||(EOLine==1&&(abs(Ix-RUNval)>NEAR)))/*情况1：被不同象素中断*/
		{
		output=output<<1;
		cnt1++;
        output=(output<<(J[RUNindex]))+RUNcnt;/*之前已经写入最逼近RUNlen的rm段，再左移一个rm段后，加入剩RUNlen下的部分*/
		cnt1=cnt1+J[RUNindex];
		if(RUNindex>0)
			RUNindex--;
		}
		else if(RUNcnt>0)/*情况2：被行末尾中断*/
		{
			output=(output<<1)+1;
			cnt1++;
		}
	    pp=cnt;
		cnt=cnt+cnt1; 		
        writecode(&cnt,&pp,&output,&code);
	    if(EOLine==1&&(abs(Ix-RUNval)<=NEAR))
			return;/*由于行的末尾终止，可正常结束，跳出此次游程模式*/
		if(abs(Ra-Rb)<=NEAR)
			RItype=1;
		else
			RItype=0;
		if(RItype==1)
			Px=Ra;
		else
			Px=Rb;
		Errval=Ix-Px;    
        if((RItype==0)&&(Ra>Rb))
		{
	     Errval=-Errval;
	     SIGN=-1;
		}
        else		
			SIGN=1;
		if(NEAR>0){
		 if(Errval>0)
		   Errval=(Errval+NEAR)/(2*NEAR+1);
	     else
		   Errval=-(NEAR-Errval)/(2*NEAR+1);
	     Rx=Px+SIGN*Errval*(2*NEAR+1);
	        if(Rx<0)
		     Rx=0;
        	else if(Rx>MAXVAL)
				Rx=MAXVAL;
		}
		else
			Rx=Ix;
         *(f+LinX*(y+2)+RowX)=Rx;
        Errval=ModRange(Errval);
	    if(RItype==0)
		TEMP=A[365];
    	else
		TEMP=A[366]+(N[366]>>1);
	    Q=RItype+365;
        AQ=A[Q];/*将当前A[Q]暂存，借用完LG(Q)后还可进行正常操作*/	
	    A[Q]=TEMP;
		k=LG(Q);
	   
	   
		if((k==0)&&(Errval>0)&&(2*Nn[Q-365]<N[Q]))
			map=1;
		else if((Errval<0)&&(2*Nn[Q-365]>=N[Q]))
			map=1;
		else if((Errval<0)&&(k!=0))
			map=1;
		else 
			map=0;
        
	    EMErrval=2*abs(Errval)-RItype-map;/*游程中断编码*/
	    glimit=LIMIT-J[RUNindex]-1;
	    interim=EMErrval;
 		interim=interim>>k;
		if(interim<((unsigned)(glimit-qbpp-1)))
		{
			unsigned b,c;
			output=0;
			c=~(~0<<k);
			b=c&EMErrval;
   			output=(output<<(interim+1))+1;
   			output=output<<k;
			output=output+b;
            pp=cnt;
			cnt=cnt+interim+1+k; 		
            writecode(&cnt,&pp,&output,&code); 
		}
		else
		{
			unsigned b,c;
			output=0;
			output=(output<<(glimit-qbpp))+1;
			output=output<<qbpp;
			c=~(~0<<qbpp);
			b=c&(EMErrval-1);
			output=output+b;
            pp=cnt;
			cnt=cnt+glimit; 		
            writecode(&cnt,&pp,&output,&code);
		}
//      ***********************		
//      *    更新各个变量     *
//      ***********************
		if(Errval<0)
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
//                  *                    主程序                     *
//                  *************************************************

//     i,j:循环变量计数；
//	   _______________________
//     |   | Rc| Rb| Rd|   |
//     -----------------------           
//	   |   | Ra| Ix|   |   |
//	   -----------------------	
//     D1,D2,D3:当前梯度
//     x,y:图像的高度和宽度

void main()
{
	int i,j,Ra,Rb,Rc,Rd,Ix,D1,D2,D3;
	int x,y;
    int BASIC_T1=3,BASIC_T2=7,BASIC_T3=21;
	float T1,T2,T3;
	struct timeb start_time,end_time;
	int second_d;
 	printf("图象高度和宽度\n");
	scanf("%d,%d",&x,&y);
	ftime(&start_time);
	f=(int *)calloc((x+1)*(y+2),sizeof(int)); /*补零后的图像多两列，一行*/
 //  if((fp=fopen("E:\\felicia\\adata7.raw","rb"))==NULL)
    if((fp=fopen("e:\\felicia\\LENA128.RAW","rb"))==NULL)
	   {	  
		 printf("Error opening %s","e:\\felicia\\TU1.raw");
		 exit(0);
	   }
//            *********************************
//            *       计算各参数的值          *
//            *********************************	
	for(i=1;i<=x;i++)
		for(j=1;j<=y;j++){
			fread(f+i*(y+2)+j,1,1,fp);/*前面空一行，以作重建值。从第二行写起。此时补的行还是零，到后面预测时补入Rb等。*/
            if(*(f+i*(y+2)+j)>MAXVAL)
				MAXVAL=*(f+i*(y+2)+j);/*先求实际最大值*/
			
		}

		for(i=0;(1<<i)<=MAXVAL;i++);
		MAXVAL=(1<<i)-1;/*规整到2的n次方故取大于实际MAXVAL的最小2的n次方*/
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
    
//       ******************************		
//       *     对各数组的初始化       *
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
	
	for(i=0;i<y+3;i++)
		*(f+i)=0;/*第一行及第二行第一个全为零*/
        
    fp=fopen("E:\\felicia\\Adata2","wb");
//    ************************	
//    *      读入变量        *
//    ************************
	while(RowX<=y&&LinX<=x)/*到计算时间之前为大循环，一个一个象素处理*/
	{   
    Ra=(*(f+LinX*(y+2)+RowX-1));
	Rb=(*(f+(LinX-1)*(y+2)+RowX));
    Rc=(*(f+(LinX-1)*(y+2)+RowX-1));
	Rd=(*(f+(LinX-1)*(y+2)+RowX+1));
	Ix=(*(f+LinX*(y+2)+RowX));
    D1=Rd-Rb;
	D2=Rb-Rc;
	D3=Rc-Ra;
//   ******************************    
//   *       选择编码方式         *
//   ******************************	
	if((abs(D1)<=NEAR)&&(abs(D2)<=NEAR)&&(abs(D3)<=NEAR))
		RunModeProcessing(x,y,Ra,Rb,Rc,Rd,Ix);
    	else
		RegularModeProcessing(y,Ra,Rb,Rc,Rd,Ix,D1,D2,D3,T1,T2,T3);
	    RowX++;
		if(RowX==y)/*原图像一行的结尾（是补零后的倒数第二个象素）*/
      	{
		*(f+(LinX+1)*(y+2))=*(f+LinX*(y+2)+1);/*处理下一行的第一个象素的上下文：将Rb赋给a*/
    	*(f+LinX*(y+2)+y+1)=*(f+LinX*(y+2)+y);/*处理当前行最后一个象素的上下文：将Rb赋给d*/
		 EOLine=1;
		}
		else
        EOLine=0;   
    	if(RowX>y)/*补零后的最后一个象素*/
		{
		RowX=RowX-y;/*也即rowx＝1*/
		LinX++;
		}
	}
#if 0
	printf("出现Errval小于零%d次\n",z);
#endif
	if(cnt>0)
		code=code<<(8-cnt);
    fwrite(&code,1,1,fp);
	fclose(fp);
	ftime(&end_time);
//     **************************
//     *      计算编码时间      *
//     **************************	
	second_d=end_time.millitm-start_time.millitm;
	second_d=second_d+(end_time.time-start_time.time)*1000;
	printf("The encoding costs:%.3f seconds.\n",(float)second_d/1000.0);
//     ***************************
//     *      图像原始数据       *
//     ***************************
	fp=fopen("E:\\felicia\\Adata4.dat","w");
    for( i=0;i<=x;i++){
	    for(j=0;j<=y+1;j++)
			fprintf(fp,"%5d",*(f+i*(y+2)+j));
	        fprintf(fp,"\n");
	}
	fclose(fp);
/*	fp=fopen("E:\\felicia\\Adata6.dat","w");
    for(j=0;j<=y+1;j++){
	    for(i=0;i<=x;i++)
			fprintf(fp,"%5d",*(f+j*(x+1)+i));
	        fprintf(fp,"\n");
	}
	fclose(fp);*/
//	fp=fopen("E:\\felicia\\Adata5.dat","w");
//  for( i=0;i<=364;i++){
	   
//			fprintf(fp,"%5d\n",Nt[i]);
//	       	}
//	fclose(fp);
} 