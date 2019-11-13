#Thesis code
#Portfolio selection through copula parameter estimation and Penalization Regression
#####Import and load all libraries####
library(quadprog)
#install.packages('stringr')
#install.packages("reshape2", repos="http://cran.rstudio.com/", dependencies=TRUE)
library(reshape2)
library(timeDate)
library(fBasics)
library(zoo)
library(xts)
library(FinTS)
library(tseries)
#install.packages('bindrcpp',type="binary",dependencies=TRUE)
library(tidyverse)
#install.packages('recipes',type="binary",dependencies=TRUE)
library(caret)
library(glmnet)
library(psych)
library(glasso)
library(CVglasso)
#install.packages('CVglasso',dependencies=TRUE)
library(huge)
#install.packages('devtools',type='binary',dependencies=TRUE)
library(devtools)
#install.packages("truncnorm", type = "binary")
#install.packages("slam", type = "binary")
library(fPortfolio)
library(timeSeries)
library(rvest)
library(quantmod)
library(TTR)
library(expm)
library(plyr)
library(PerformanceAnalytics)
#install.packages("MFTSR", repos="http://R-Forge.R-project.org")
library(MFTSR)
library(RiskPortfolios)
##### Step 0: Data retrieval and initialization####
#Obtain the 500 stocks that are today within the S&P 500
tbl <- read_html('https://en.wikipedia.org/wiki/List_of_S%26P_500_companies') %>% html_nodes(css = 'table')
tbl <- tbl[1] %>% html_table() %>% as.data.frame()
tbl$Symbol <- gsub(pattern = '\\.', '-', tbl$Symbol) # BRK.B -> BRK-B (yahoo uses '-')
head(tbl$Symbol)

#Retieve all prices for the 500 stocks in S&P 500 since 1-Jan-2007
prices = Map(function(n)
{
  print(n)
  tryCatch(getSymbols(n, src="yahoo", env=NULL, from='2008-01-01')[, 6], error = function(e) NA)
}, tbl$Symbol)

N = length(prices)
# identify symbols returning valid data
i = ! unlist(Map(function(i) is.na(prices[i]), seq(N)))
# combine returned prices list into a matrix, one column for each symbol with valid data
prices = Reduce(cbind, prices[i])
colnames(prices) = tbl$Symbol[i]
m=dim(prices)[2]
miss=c()
#Identify which stocks have missing values
for(j in 1:ncol(prices))
{
  miss[j]=sum(is.na(prices[,j]))
}
tickers=tbl[1]
stocks_na=tickers[miss!=0,1]
length(stocks_na)
pricesDF=as.data.frame(prices)
#There are aproximately 65 stocks with incomplete data since early 2007
#We proceed to eliminate stocks with missing data, obtaining a complete dataset
table_na=pricesDF[stocks_na]
pricesAdj=pricesDF[,!(names(pricesDF) %in% stocks_na)]

#We desire to evaluate our models performances by dividing the data into two
#From 01-Jan-2007 till 1 year from now, we'll have the training set. 
#The test set will be 252 days from today until today (252 data points)
size=1*nrow(pricesAdj)
brake=1*(size-252)
#Testing set
pricesAdj_CW=pricesAdj[(brake+1):size,]
#Training set
pricesAdj=pricesAdj[1:brake,]
#REVISAR ESTO!!!!!
#LHX apparently has some data issues, all the prices appear to be negative, we proceed to eliminate this stock
#Debido a que la acción LHX está generando NaNs por el negativo que tienen sus valores, se elimina
#prices = subset(prices, select = -c(LHX) )
#Finally, we obtain the logarithmic returns of the prices for each stock
#in both the training and the test set
log_returns = apply(pricesAdj, 2, function(x) diff(log(x)))
log_returns_CW =apply(pricesAdj_CW, 2, function(x) diff(log(x)))

#We must make sure our data is clean, we check for any NaN values in the log_returns
#NaNs in our data would possibly indicate that some stock prices are negative, these problematic stocks
#are to be eliminated.
log_returns1=c()
for(m in 1:ncol(pricesAdj)){
  log_returns1[m]=sum(is.na(diff(log(pricesAdj[,m]))))
}
sum(log_returns1)
#Finally, we have a clean dataset

######Model 0:Naive approach#######
#We obtain the weights for the Naive approach (1/N)
p=ncol(log_returns)
wNaive=rep(1/p,p)
sum(wNaive)
######Model 1: Markowitz traditional approach  #####
n=nrow(log_returns)
p=ncol(log_returns)
av_coef=2.5
#average returns vector (miu)
miu=(1/n)*matrix(1,1,n)%*%log_returns
miu=t(miu)
#variance-covariance matrix estimation (S)
C=diag(n)-matrix(1/n,n,n)
Xc=C %*% log_returns
S=(t(Xc)%*%Xc)/(n-1)


#We want to prove that this matrix is positive semidefinite
ev= eigen(S)
eigenValues= ev$values
NONEGATIVOS=TRUE
for(i in 1:p){
  if(eigenValues[i]<0){
    NONEGATIVOS=FALSE
  }
}
NONEGATIVOS
#As all eigenvalues are positive, we can conclude that our matix is positive semidefinite
#So its inverse has a solution


#Function: traditionalMarkowitzForced
#Description: The function returns the long-only Markowitz traditional portfolio weights,
#due to long-only restriction, negative values are forced to be 0, the model is then
#recalibrated to sum 1.
#Inputs: aversion_coef: The aversion coefficient
#Omega: Inverse variance-covariance matrix (precision matrix)
#m: The vector of average returns
#Output: (px1 vector) Markowitz model weights with forced positivity restriction
traditionalMarkowitzForced=function(aversion_coef,Omega,m){
  p=dim(Omega)[1]
  wMarkowitz_restr_sum_1= (1/aversion_coef)*Omega%*%(m-((((matrix(1,1,p)%*%Omega%*%m)-aversion_coef)/(matrix(1,1,p)%*%Omega%*%matrix(1,p,1)))[1,1]*matrix(1,p,1)))
  w_Mark_Forced=c()
  for(i in 1:length(wMarkowitz_restr_sum_1)){
    if(wMarkowitz_restr_sum_1[i]<0){
      w_Mark_Forced[i]=0
    }
    else{
      w_Mark_Forced[i]=wMarkowitz_restr_sum_1[i]
    }
  }
  w_Mark_Forced=w_Mark_Forced/sum(w_Mark_Forced)
  return (w_Mark_Forced)
  }

w_Mark_Forced=traditionalMarkowitzForced(av_coef,solve(S),miu)

#Considering another approach to obtain the Markowitz traditional weights
#without the need of a forced positivity constraint, we decide to try the 
#optimization approach (Quadratic optimization) with long only constraint
#Function: traditionalMarkowitzOptimization
#Description: The function returns the long-only Markowitz traditional portfolio weights,
#due to long-only restriction, we create a quadratic optimization problem:
#Optimization problem: minimize  (av_coef/2)*w^{T} \Sigma w - R^{T}w. 
#s.t. \sum w_i = 1 and w_i>=0 forall i in p
#Inputs: aversion_coef: The aversion coefficient
#Sigma: Variance-covariance matrix
#m: The vector of average returns
#Output: (px1 vector) Markowitz model weights with optimization 
traditionalMarkowitzOptimization=function(aversion_coef,Sigma,m){
  p=dim(Sigma)[1]
  Dmat=(Sigma*aversion_coef)
  dvec=m
  Amat=cbind(1,diag(p))
  bvec=c(1,rep(0,p))
  qp <- solve.QP(Dmat=Dmat, dvec=dvec, Amat=Amat, bvec=bvec, meq=1)
  #We obtain the solution to the optimization problem
  w_Mark_Opti=qp$solution
  return(w_Mark_Opti)
}
w_Mark_Opti=traditionalMarkowitzOptimization(av_coef,S,miu)

#####Model 2: Markowitz Regression with Penalization ####
#We create a function that give us the weights applying regression to 
#portfolio problem and shrinking the estimators through L1 or L2 penalization

#Function: markowitzRegressionPenalization
#Description: The function returns the long-only Markowitz regression portfolio weights,
#by first obtaining the regression problem mentioned by (Jiahan Li) and then
#applying shrinkage to these estimated coefficients through penalization
#the user chooses to run Ridge or Lasso penalization.
#Inputs: aversion_coef: The aversion coefficient
#Sigma: Variance-covariance matrix
#Omega: Inverse of variance-covariance matrix (precision matrix)
#m: The vector of average returns
#alph: Binary parameter for penalization. 0-> Ridge. 1->Lasso
#n_fold: Number of folds for cross-validation during penlaization.
#recommended value= p/3
#Output: (px1 vector) Markowitz Regression model weights with penalization chosen in alph (Ridge or Lasso)
markowitzRegressionPenalization=function(aversion_coef,Sigma,Omega,m,alph,n_fold){
  sqrt_sigma=sqrtm(Sigma)
  sqrt_omega=sqrtm(Omega)
  #We obtain X and Y for a linear regression model suggested by Li
  X=sqrt(aversion_coef)*sqrt_sigma
  Y=sqrt(1/aversion_coef)*sqrt_omega%*%m
  #YWe proceed to apply sparse statistic methods (Penalization)
  cvmod=cv.glmnet(X,Y,alpha=alph,nfolds=n_fold,intercept=FALSE,lower.limits = 0)
  mod_pen2=glmnet(X,Y,alpha=alph,lambda=cvmod$lambda.min, intercept = FALSE,lower.limits = 0)
  wPenali=as.matrix(coef(mod_pen2))
  wPenali=wPenali[2:length(wPenali)*1]
  wPenali=wPenali/((sum(wPenali)))
  return(wPenali)
}

wRidge=markowitzRegressionPenalization(av_coef,S,solve(S),miu,0,(p/3))
wLasso=markowitzRegressionPenalization(av_coef,S,solve(S),miu,1,(p/3))


#####Model 3: Copula variance covariance matrix estimation and application####

#Function: copula
#Description: The copula function returns a variance covariance matrix of a given data, 
#using the algorithm described by John Lafferty, Han Liu and Larry Wasserman
#in the paper in Sparse Nonparametric Graphical Models (pg. 5)
#Inputs: log_ret: data that will be used for the estimation
#delta: The truncation parameter mentioned in the paper for a Winzorized 
#truncation: Recommended: 1/((4*(n^(1/4)))*(sqrt(pi*log(n)))) 
#where n is the # of rows of the input data (log_ret)
#Output: (pxp matrix) Estimated pxp variance-covariance matrix using copula and nonparanormal algorithm
copula=function(log_ret,delta){
  F_hat= function(j,t,n,X){
    total=0
    for (i in 1:n){
      if(X[i,j]<=t){
        total=total+1
        #X[i,j] is X_j^i, represents jth stock return on the ith day. 
      }
    }
    return ((1/n)*total)
  }
  
  F_tilde=function(j,x,n,Wdelta,X){
    ans=0
    tempo=F_hat(j,x,n,X)
    if(tempo<Wdelta){
      ans=Wdelta
    }
    else if(tempo>=Wdelta & tempo<=(1-Wdelta)){
      ans=tempo
    }
    else {
      ans=(1-Wdelta)
    }
    return (ans)
  }
  
  h_hat=function(j,x,n,Wdelta,X){
    ans=qnorm(F_tilde(j,x,n,Wdelta,X),0,1)
    return(ans)
  }
  
  f_tilde=function(j,x,n,Wdelta,X){
    mu=mean(X[,j])
    sigma=sd(X[,j])
    return (mu+sigma*h_hat(j,x,n,Wdelta,X))
  }
  
  #X^1 is X[1,]
  #Xsuper1=log_returns[1,]
  d=dim(log_ret)[2]*1
  n=dim(log_ret)[1]*1
  #intento para el primer vector f(X^1)
  #vector=rep(0,d)
  #for (j in 1:d){
  #  vector[j]=f_tilde(j,log_returns[2,j],n,delta,log_returns)
  #}
  
  #Calculate the mean for each f(X)
  f_tilde_i_n=matrix(rep(0,n*d),nrow=d,ncol = n)
  for(i in 1:n){
    for (j in 1:d){
      f_tilde_i_n[j,i]=f_tilde(j,log_ret[i,j],n,delta,log_ret)
      
    } 
    if((i%%round((n/100),digits=0)==0)){
      print(paste(round((i/n),digits = 2)*100,"%"))
    }
  }
  
  mu_f=(1/n)*rowSums(f_tilde_i_n)
  #We obtain miu (mean), now we estimate the variance covariance matrix
  matriz=matrix(rep(0,d*d),nrow=d,ncol = d)
  for(i in 1:n){
    vector=f_tilde_i_n[,i]-mu_f
    matriz=matriz+(vector%*%t(vector))
  }
  var_cov_copula=(1/n)*matriz
  
  return(var_cov_copula)
}

var_cov_copula=copula(log_returns,1/((4*(n^(1/4)))*(sqrt(pi*log(n)))))

#We proceed to estimate the portfolio weights for the different model approaches
#above, but this time using the estimated variance covariance matrix using copulas
#First, we must use Glasso to estimate the inverse of the variance-covariance matrix.

#log_returns.norm=scale(log_returns)
#log_returns.npn=huge.npn(log_returns.norm,npn.func = "truncation")

#We use the CVglasso library that uses cross validation to obtain a very good candidate
#for the inverse of the variance covariance matrix. 
#From now onwards, we will refer to the inverse of the variance covariance
#matrix as the precision matrix. 
precision_glasso_copula_m=CVglasso(X=log_returns,S=var_cov_copula,lam.min.ratio = 1e-3)
#With lam.min.ratio=1e-3, we have arrived to a optimal tuning parameter thats not on boundary
precision_glasso_copula=precision_glasso_copula_m$Omega
var_cov_glasso_copula=precision_glasso_copula_m$Sigma
#PREGUNTAR A CARLOS SI TIENE SENTIDO UTILIZAR LA COPULA ESTIMADA Y NO LA PENALIZADA POR GLASSO
#PREGUNTAR A CARLOS, PORQUE DA TAN MAL CUANDO SE TRATA DE NORMALIZAR (NORMAL SCORES)
#Model 3.1: Markowitz forced traditional approach with copula & glasso var-cov and precision matrices
w_Mark_Forced_glasso_copula=traditionalMarkowitzForced(av_coef,precision_glasso_copula,miu)
#Model 3.2: Markowitz optimization traditional approach with copula & glasso var-cov and precision matrices
w_Mark_Opti_glasso_copula=traditionalMarkowitzOptimization(av_coef,var_cov_glasso_copula,miu)
#Model 3.3: Markowitz Regression with Penalization with copula & glasso var-cov and precision matrices
#Ridge model
wRidge_glasso_copula=markowitzRegressionPenalization(av_coef,var_cov_glasso_copula,precision_glasso_copula,miu,0,(p/3))
#Lasso model
wLasso_glasso_copula=markowitzRegressionPenalization(av_coef,var_cov_glasso_copula,precision_glasso_copula,miu,1,(p/3))

#####Model 4: Glasso estimation of variance covariance matrix (Simply to check the effect of using the copula estimated var-cov)######
#log_returns.npn=huge.npn(log_returns,npn.func = "truncation")
#Estimate the glasso
#out.npn=huge(var_cov,method = "glasso",nlambda=40,lambda.min.ratio = 0.4)
#npn.ric = huge.select(out.npn)
#precision_glasso=as.matrix(out.npn[["icov"]][[40]])
#rho=seq(0,10,by=0.01)
#precision_glasso=glasso(var_cov,0.01)$wi
#var_cov_glasso=glasso(var_cov,0.01)$w
#var_cov_norm=cov(log_returns.npn)
precision_glasso_m=CVglasso(X=log_returns,S=S,lam.min.ratio = 1e-3)
precision_glasso=precision_glasso_m$Omega
var_cov_glasso=precision_glasso_m$Sigma

#Model 4.1: Markowitz forced traditional approach with glasso var-cov and precision matrices
w_Mark_Forced_glasso=traditionalMarkowitzForced(av_coef,precision_glasso,miu)
#Model 4.2: Markowitz optimization traditional approach with glasso var-cov and precision matrices
w_Mark_Opti_glasso=traditionalMarkowitzOptimization(av_coef,var_cov_glasso,miu)
#Model 4.3: Markowitz Regression with Penalization with glasso var-cov and precision matrices
#Ridge model
wRidge_glasso=markowitzRegressionPenalization(av_coef,var_cov_glasso,precision_glasso,miu,0,(p/3))
#Lasso model
wLasso_glasso=markowitzRegressionPenalization(av_coef,var_cov_glasso,precision_glasso,miu,1,(p/3))

#####Model Validation Cumulative Wealth#####
#We will break down graphs by method, the last graph will be a comparison
#between the best candidates of each method
#Function: cummulative Wealth
#Description: The CW function returns a vector containing the cummulaitve wealth obtained with the inputed portfolio, 
#Inputs: log_ret: data that will be used for the estimation
#portfolio: Portfolio to evaluate 

#Output: (nx1 vector) The series of cummulative weights from time=1 to n (size of log_ret)
cw=function(log_ret,portfolio){
  CW=c()
  t=nrow(log_ret)
  CW[1]=1
  for(i in 1:t){
    Rt=t(portfolio)%*%as.matrix(log_ret[i,])
    CW[i+1]=CW[i]*(1+Rt[1,1])
  }
  return (CW)
}


#We create the time series
Te=c()
t=nrow(log_returns_CW)
Te[1]=1
for(i in 1:t){
  Te[i+1]=i+1
}
#Graph #1: Markowitz traditional approach with optimization problem
#Line 1.0: Naive approach (reference)
Naive=cw(log_returns_CW,wNaive)
#Line 1.1: Markowitz traditional approach with optimization problem (using S as var-cov)
Mark_Opt.S=as.data.frame(cw(log_returns_CW,w_Mark_Opti))
colnames(Mark_Opt.S)="Mark_Opt.S"
#Line 1.2: Markowitz traditional approach with copula var-cov glasso optimization problem
Mark_Opt.C=as.data.frame(cw(log_returns_CW,w_Mark_Opti_glasso_copula))
colnames(Mark_Opt.C)="Mark_Opt.C"
#Line 1.3: Markowitz traditional approach with var-cov glasso optimization problem
Mark_Opt.G=as.data.frame(cw(log_returns_CW,w_Mark_Opti_glasso))
colnames(Mark_Opt.G)="Mark_Opt.G"
#Graph the results
CW1=as.data.frame(cbind(Te,Naive,Mark_Opt.S,Mark_Opt.G,Mark_Opt.C))
CW1=melt(CW1,id=c('Te'))
CW1=cbind(CW1,c(rep("Naive",252),rep("SS",252),rep("GLASSO",252),rep("Copula GLASSO",252)))
names(CW1)=c("Te","variable","value","CovarianceMatrix")
CW1$CovarianceMatrix=factor(CW1$CovarianceMatrix,levels=c("Naive","SS","GLASSO","Copula GLASSO"))
jpeg("CW_Mark_Opt_2008_G.jpg", width = 1081.5, height = 1215)
ggplot(CW1) +geom_line(aes(x = Te, y = value ,color=CovarianceMatrix))+labs(title="Cumulative Wealth Index",subtitle="Markowitz Mean-variance Optimization Model",x="Time (252 trading days)",y="Cumulative Wealth Index",colour="CovarianceMatrix")+ theme(legend.position = c(0.8, 0.2),legend.title = element_text(size = 25),legend.text = element_text(size = 22),legend.key.size = unit(4,"line"),axis.text=element_text(size=18),axis.title=element_text(size=30,face="bold"),plot.title = element_text(size=26,face="bold"),plot.subtitle = element_text(size=22))
dev.off()
#Graph #2: Markowitz traditional approach with forced restiriction long only
#Line 2.0: Naive approach (reference)
Naive=cw(log_returns_CW,wNaive)
#Line 2.1: Markowitz traditional approach with forced restiriction long only (using S as var-cov)
Mark_Forced.S=cw(log_returns_CW,w_Mark_Forced)
#Line 2.2: Markowitz traditional approch with copula var-cov glasso forced resticction long only
Mark_Forced.C=cw(log_returns_CW,w_Mark_Forced_glasso_copula)
#Line 2.3: Markowitz traditional with var-cov glasso forced resticction long only
Mark_Forced.G=cw(log_returns_CW,w_Mark_Forced_glasso)
#Graph the results
CW2=as.data.frame(cbind(Te,Naive,Mark_Forced.S,Mark_Forced.G,Mark_Forced.C))
CW2=melt(CW2,id=c('Te'))
CW2=cbind(CW2,c(rep("Naive",252),rep("SS",252),rep("GLASSO",252),rep("Copula GLASSO",252)))
names(CW2)=c("Te","variable","value","CovarianceMatrix")
CW2$CovarianceMatrix=factor(CW2$CovarianceMatrix,levels=c("Naive","SS","GLASSO","Copula GLASSO"))
jpeg("CW_Mark_Forced_2008_G.jpg", width = 1081.5, height = 1215)
ggplot(CW2) +geom_line(aes(x = Te, y = value ,color=CovarianceMatrix))+labs(title="Cumulative Wealth Index",subtitle="Markowitz Mean-variance Forced Model",x="Time (252 trading days)",y="Cumulative Wealth Index",colour="CovarianceMatrix")+ theme(legend.position = c(0.8, 0.2),legend.title = element_text(size = 25),legend.text = element_text(size = 22),legend.key.size = unit(4,"line"),axis.text=element_text(size=18),axis.title=element_text(size=30,face="bold"),plot.title = element_text(size=26,face="bold"),plot.subtitle = element_text(size=22))
dev.off()
#Graph #3: Markowitz regression Ridge approach
#Line 3.0: Naive approach (reference)
Naive=cw(log_returns_CW,wNaive)
#Line 3.1: Markowitz regression Ridge approach (with S as var-cov)
Ridge.S=cw(log_returns_CW,wRidge)
#Line 3.2: Markowitz regression Ridge approach with copula var-cov glasso
Ridge.C=cw(log_returns_CW,wRidge_glasso_copula)
#Line 3.3: Markowitz regression Ridge approach with var-cov glasso
Ridge.G=cw(log_returns_CW,wRidge_glasso)
#Graph the results
CW3=as.data.frame(cbind(Te,Naive,Ridge.S,Ridge.G,Ridge.C))
CW3=melt(CW3,id=c('Te'))
CW3=cbind(CW3,c(rep("Naive",252),rep("SS",252),rep("GLASSO",252),rep("Copula GLASSO",252)))
names(CW3)=c("Te","variable","value","CovarianceMatrix")
CW3$CovarianceMatrix=factor(CW3$CovarianceMatrix,levels=c("Naive","SS","GLASSO","Copula GLASSO"))
jpeg("CW_Ridge_2008_G.jpg", width = 1081.5, height = 1215)
ggplot(CW3) +geom_line(aes(x = Te, y = value ,color=CovarianceMatrix))+labs(title="Cumulative Wealth Index",subtitle="Ridge Regression Model",x="Time (252 trading days)",y="Cumulative Wealth Index",colour="CovarianceMatrix")+ theme(legend.position = c(0.8, 0.2),legend.title = element_text(size = 25),legend.text = element_text(size = 22),legend.key.size = unit(4,"line"),axis.text=element_text(size=18),axis.title=element_text(size=30,face="bold"),plot.title = element_text(size=26,face="bold"),plot.subtitle = element_text(size=22))
dev.off()

#Graph 4: Markowitz regression Lasso approach
#Line 4.0: Naive approach (reference)
Naive=cw(log_returns_CW,wNaive)
#Line 4.1: Markowitz regression Lasso approach (using S as var-cov)
Lasso.S=cw(log_returns_CW,wLasso)
#Line 4.2: Markowitz regression Lasso approach with copula var-cov glasso
Lasso.C=cw(log_returns_CW,wLasso_glasso_copula)
#Line 4.3: Markowitz regression LASSO approach with var-cov glasso
Lasso.G=cw(log_returns_CW,wLasso_glasso)
#Graph the results
CW4=as.data.frame(cbind(Te,Naive,Lasso.S,Lasso.G,Lasso.C))
CW4=melt(CW4,id=c('Te'))
CW4=cbind(CW4,c(rep("Naive",252),rep("SS",252),rep("GLASSO",252),rep("Copula GLASSO",252)))
names(CW4)=c("Te","variable","value","CovarianceMatrix")
CW4$CovarianceMatrix=factor(CW4$CovarianceMatrix,levels=c("Naive","SS","GLASSO","Copula GLASSO"))
jpeg("CW_Lasso_2008_G.jpg", width = 1081.5, height = 1215)
ggplot(CW4) +geom_line(aes(x = Te, y = value ,color=CovarianceMatrix))+labs(title="Cumulative Wealth Index",subtitle="Lasso Regression Model",x="Time (252 trading days)",y="Cumulative Wealth Index")+ theme(legend.position = c(0.8, 0.2),legend.title = element_text(size = 25),legend.text = element_text(size = 22),legend.key.size = unit(4,"line"),axis.text=element_text(size=18),axis.title=element_text(size=30,face="bold"),plot.title = element_text(size=26,face="bold"),plot.subtitle = element_text(size=22))
dev.off()



 #Graph 5: Best line of each model in one graph for comparison

#Line 5.1: Naive approach (reference)
Naive=cw(log_returns_CW,wNaive)
CW5=as.data.frame(cbind(Te,Naive,Mark_Opt.C,Mark_Forced.G,Ridge.C,Lasso.C))
CW5=melt(CW5,id=c('Te'))
jpeg("CW_Best_2008_G.jpg", width = 1081.5, height = 1215)
ggplot(CW5) +geom_line(aes(x = Te, y = value ,color=variable))
dev.off()

#Graph 6: All models in one graph

CW6=as.data.frame(cbind(Te,Naive,Mark_Opt.S,Mark_Opt.G,Mark_Opt.C,Mark_Forced.S,Mark_Forced.G,Mark_Forced.C,Ridge.S,Ridge.G,Ridge.C,Lasso.S,Lasso.G,Lasso.C))
#Range analysis at end of year
CW6_Range=CW6[201:252,]
min_benchmark=min(min(CW6_Range$Naive,CW6_Range$Mark_Opt.S,CW6_Range$Mark_Opt.G,CW6_Range$Mark_Opt.C,CW6_Range$Mark_Forced.S,CW6_Range$Mark_Forced.G,CW6_Range$Mark_Forced.C))
max_benchmark=max(max(CW6_Range$Naive,CW6_Range$Mark_Opt.S,CW6_Range$Mark_Opt.G,CW6_Range$Mark_Opt.C,CW6_Range$Mark_Forced.S,CW6_Range$Mark_Forced.G,CW6_Range$Mark_Forced.C))
min_penalization=min(min(CW6_Range$Ridge.S,CW6_Range$Ridge.G,CW6_Range$Ridge.C,CW6_Range$Lasso.S,CW6_Range$Lasso.G,CW6_Range$Lasso.C))
max_penalization=max(max(CW6_Range$Ridge.S,CW6_Range$Ridge.G,CW6_Range$Ridge.C,CW6_Range$Lasso.S,CW6_Range$Lasso.G,CW6_Range$Lasso.C))


summary(CW6_Range)
CW6=melt(CW6,id=c('Te'))
CW6=cbind(CW6,c(rep("Naive",252),rep("Mark_Opt",756),rep("Mark_Forced",756),rep("Ridge",756),rep("Lasso",756)))
CW6=cbind(CW6,c(rep("SS",252),rep("SS",252),rep("GLASSO",252),rep("Copula GLASSO",252),rep("SS",252),rep("GLASSO",252),rep("Copula GLASSO",252),rep("SS",252),rep("GLASSO",252),rep("Copula GLASSO",252),rep("SS",252),rep("GLASSO",252),rep("Copula GLASSO",252)))
names(CW6)=c("Te","variable","value","Model","CovarianceMatrix")
CW6$CovarianceMatrix=factor(CW6$CovarianceMatrix,levels=c("SS","GLASSO","Copula GLASSO"))
CW6$Model=factor(CW6$Model,levels=c("Naive","Mark_Opt","Mark_Forced","Ridge","Lasso"))
jpeg("CW_All_2008_G.jpg",  width = 1081.5, height = 1215)
ggplot(CW6,aes(x = Te, y = value)) +geom_line(aes(x = Te, y = value ,color=Model,linetype=CovarianceMatrix))+scale_linetype_manual(values=c("dashed", "dotdash","solid")) +labs(title="Cumulative Wealth Index",subtitle="All models",x="Time (252 trading days)",y="Cumulative Wealth Index")+ theme(legend.position = c(0.8, 0.25),legend.title = element_text(size = 25),legend.text = element_text(size = 22),legend.key.size = unit(3,"line"),axis.text=element_text(size=18),axis.title=element_text(size=30,face="bold"),plot.title = element_text(size=26,face="bold"),plot.subtitle = element_text(size=22))
dev.off()



#####Model Validation Sharpe Ratio####
#Function: sharpe Ratio
#Description: The SR function returns a scalar representing the sharpe ratio according with the inputed parameters
#Inputs: log_ret: data that will be used for the estimation
#portfolio: Portfolio to evaluate 
#rf: Risk-free rate to consider 
#We calculate the risk-free as the annual average return of a US 1 year
#t-bill: 2.31%

#Output: (scalar) The calculated sharpe ratio
sr=function(log_ret,portfolio,rf){
  n=nrow(log_ret)
  p=ncol(log_ret)
  Rt=c()
  #for(i in 1:n){
  #  Rt[i]=t(portfolio)%*%as.matrix(log_ret[i,])
  #}
  Rt=Return.portfolio(log_ret,portfolio)
  RF=rep(rf,n)
  excess=Rt-RF
  SD=sd(excess)*sqrt(252)
  MU=mean(excess)*252
  SR=MU/SD
  list=list(SR,MU,SD)
  return (list)
}

Risk_free=0.0231
#Graph #1: Markowitz traditional approach with optimization problem
#Line 1.1: Markowitz traditional approach with optimization problem (using S as var-cov)
ret=Return.portfolio(log_returns_CW,w_Mark_Opti)
Mark_Opt.S_SR=SharpeRatio.annualized(ret, Rf = (Risk_free/252), scale = 252, geometric=TRUE)
#Line 1.2: Markowitz traditional approach with copula var-cov glasso optimization problem
ret=Return.portfolio(log_returns_CW,w_Mark_Opti_glasso_copula)
Mark_Opt.C_SR=SharpeRatio.annualized(ret, Rf = (Risk_free/252), scale = 252, geometric=TRUE)
#Line 1.3: Markowitz traditional approach with var-cov glasso optimization problem
ret=Return.portfolio(log_returns_CW,w_Mark_Opti_glasso)
Mark_Opt.G_SR=SharpeRatio.annualized(ret, Rf = (Risk_free/252), scale = 252, geometric=TRUE)

#Graph #2: Markowitz traditional approach with forced restiriction long only
#Line 2.1: Markowitz traditional approach with forced restiriction long only (using S as var-cov)
ret=Return.portfolio(log_returns_CW,w_Mark_Forced)
Mark_Forced.S_SR=SharpeRatio.annualized(ret, Rf = (Risk_free/252), scale = 252, geometric=TRUE)
#Line 2.2: Markowitz traditional approch with copula var-cov glasso forced resticction long only
ret=Return.portfolio(log_returns_CW,w_Mark_Forced_glasso_copula)
Mark_Forced.C_SR=SharpeRatio.annualized(ret, Rf = (Risk_free/252), scale = 252, geometric=TRUE)
#Line 2.3: Markowitz traditional with var-cov glasso forced resticction long only
ret=Return.portfolio(log_returns_CW,w_Mark_Forced_glasso)
Mark_Forced.G_SR=SharpeRatio.annualized(ret, Rf = (Risk_free/252), scale = 252, geometric=TRUE)

#Graph #3: Markowitz regression Ridge approach
#Line 3.1: Markowitz regression Ridge approach (with S as var-cov)
ret=Return.portfolio(log_returns_CW,wRidge)
Ridge.S_SR=SharpeRatio.annualized(ret, Rf = (Risk_free/252), scale = 252, geometric=TRUE)
#Line 3.2: Markowitz regression Ridge approach with copula var-cov glasso
ret=Return.portfolio(log_returns_CW,wRidge_glasso_copula)
Ridge.C_SR=SharpeRatio.annualized(ret, Rf = (Risk_free/252), scale = 252, geometric=TRUE)
#Line 3.3: Markowitz regression Ridge approach with var-cov glasso
ret=Return.portfolio(log_returns_CW,wRidge_glasso)
Ridge.G_SR=SharpeRatio.annualized(ret, Rf = (Risk_free/252), scale = 252, geometric=TRUE)

#Graph 4: Markowitz regression Lasso approach
#Line 4.1: Markowitz regression Lasso approach (using S as var-cov)
ret=Return.portfolio(log_returns_CW,wLasso)
Lasso.S_SR=SharpeRatio.annualized(ret, Rf = (Risk_free/252), scale = 252, geometric=TRUE)
#Line 4.2: Markowitz regression Lasso approach with copula var-cov glasso
ret=Return.portfolio(log_returns_CW,wLasso_glasso_copula)
Lasso.C_SR=SharpeRatio.annualized(ret, Rf = (Risk_free/252), scale = 252, geometric=TRUE)
#Line 4.3: Markowitz regression LASSO approach with var-cov glasso
ret=Return.portfolio(log_returns_CW,wLasso_glasso)
Lasso.G_SR=SharpeRatio.annualized(ret, Rf = (Risk_free/252), scale = 252, geometric=TRUE)


#Bar graph showing different Sharpe Ratios
Models <- c(rep("Markowitz Optimization",3), 
            rep("Markowitz Forced",3), 
            rep("Ridge",3), 
            rep("Lasso",3))

# Three covariance and precision matrices
CovarianceMatrix <- rep(c("SS","GLASSO","Copula GLASSO"),4)
SharpeRatio <- c(Mark_Opt.S_SR,Mark_Opt.G_SR,Mark_Opt.C_SR,Mark_Forced.S_SR,Mark_Forced.G_SR,Mark_Forced.C_SR,Ridge.S_SR,Ridge.G_SR,Ridge.C_SR,Lasso.S_SR,Lasso.G_SR,Lasso.C_SR)
data <- data.frame(Models,CovarianceMatrix,SharpeRatio)
data$Models=factor(data$Models,levels=c("Markowitz Optimization","Markowitz Forced","Ridge","Lasso"))
data$CovarianceMatrix=factor(data$CovarianceMatrix,levels=c("SS","GLASSO","Copula GLASSO"))
# Plot the data
jpeg("SR_2008_G.jpg", width = 1081.5, height = 1215)
ggplot(data, aes(fill=CovarianceMatrix, y=SharpeRatio , x=Models)) + geom_bar(position="dodge", stat="identity")+scale_fill_hue(l=40, c=70)+ ggtitle("Portfolio Sharpe Ratio")+theme(legend.position = c(0.2, 0.85),legend.title = element_text(size = 25),legend.text = element_text(size = 22),legend.key.size = unit(3,"line"),axis.text=element_text(size=18),axis.title=element_text(size=30,face="bold"),plot.title = element_text(size=26,face="bold"))
                                                                                                                                                                                     
dev.off()

#Bar graph showing average return
#Graph #1: Markowitz traditional approach with optimization problem
#Line 1.1: Markowitz traditional approach with optimization problem (using S as var-cov)
Mark_Opt.S_AR=sr(log_returns_CW,w_Mark_Opti,(Risk_free/252))[[2]]
#Line 1.2: Markowitz traditional approach with copula var-cov glasso optimization problem
Mark_Opt.C_AR=sr(log_returns_CW,w_Mark_Opti_glasso_copula,(Risk_free/252))[[2]]
#Line 1.3: Markowitz traditional approach with var-cov glasso optimization problem
Mark_Opt.G_AR=sr(log_returns_CW,w_Mark_Opti_glasso,(Risk_free/252))[[2]]

#Graph #2: Markowitz traditional approach with forced restiriction long only
#Line 2.1: Markowitz traditional approach with forced restiriction long only (using S as var-cov)
Mark_Forced.S_AR=sr(log_returns_CW,w_Mark_Forced,(Risk_free/252))[[2]]
#Line 2.2: Markowitz traditional approch with copula var-cov glasso forced resticction long only
Mark_Forced.C_AR=sr(log_returns_CW,w_Mark_Forced_glasso_copula,(Risk_free/252))[[2]]
#Line 2.3: Markowitz traditional with var-cov glasso forced resticction long only
Mark_Forced.G_AR=sr(log_returns_CW,w_Mark_Forced_glasso,(Risk_free/252))[[2]]

#Graph #3: Markowitz regression Ridge approach
#Line 3.1: Markowitz regression Ridge approach (with S as var-cov)
Ridge.S_AR=sr(log_returns_CW,wRidge,(Risk_free/252))[[2]]
#Line 3.2: Markowitz regression Ridge approach with copula var-cov glasso
Ridge.C_AR=sr(log_returns_CW,wRidge_glasso_copula,(Risk_free/252))[[2]]
#Line 3.3: Markowitz regression Ridge approach with var-cov glasso
Ridge.G_AR=sr(log_returns_CW,wRidge_glasso,(Risk_free/252))[[2]]

#Graph 4: Markowitz regression Lasso approach
#Line 4.1: Markowitz regression Lasso approach (using S as var-cov)
Lasso.S_AR=sr(log_returns_CW,wLasso,(Risk_free/252))[[2]]
#Line 4.2: Markowitz regression Lasso approach with copula var-cov glasso
Lasso.C_AR=sr(log_returns_CW,wLasso_glasso_copula,(Risk_free/252))[[2]]
#Line 4.3: Markowitz regression LASSO approach with var-cov glasso
Lasso.G_AR=sr(log_returns_CW,wLasso_glasso,(Risk_free/252))[[2]]

#Bar graph showing different Average returns
Models <- c(rep("Markowitz Optimization",3), 
            rep("Markowitz Forced",3), 
            rep("Ridge",3), 
            rep("Lasso",3))

# Three covariance and precision matrices
CovarianceMatrix <- rep(c("SS","GLASSO","Copula GLASSO"),4)
AverageReturn <- c(Mark_Opt.S_AR,Mark_Opt.G_AR,Mark_Opt.C_AR,Mark_Forced.S_AR,Mark_Forced.G_AR,Mark_Forced.C_AR,Ridge.S_AR,Ridge.G_AR,Ridge.C_AR,Lasso.S_AR,Lasso.G_AR,Lasso.C_AR)
data <- data.frame(Models,CovarianceMatrix,AverageReturn)
data$Models=factor(data$Models,levels=c("Markowitz Optimization","Markowitz Forced","Ridge","Lasso"))
data$CovarianceMatrix=factor(data$CovarianceMatrix,levels=c("SS","GLASSO","Copula GLASSO"))
# Plot the data
jpeg("AR_2008_G.jpg", width = 1081.5, height = 1215)
ggplot(data, aes(fill=CovarianceMatrix, y=AverageReturn , x=Models)) + geom_bar(position="dodge", stat="identity")+scale_fill_hue(l=40, c=70)+ ggtitle("Portfolio Average Returns")+theme(legend.position = c(0.1, 0.93),legend.title = element_text(size = 22),legend.text = element_text(size = 20),legend.key.size = unit(2,"line"),axis.text=element_text(size=18),axis.title=element_text(size=30,face="bold"),plot.title = element_text(size=26,face="bold"))
dev.off()

#Bar graph showing portfolios volatility
#Graph #1: Markowitz traditional approach with optimization problem
#Line 1.1: Markowitz traditional approach with optimization problem (using S as var-cov)
Mark_Opt.S_V=sr(log_returns_CW,w_Mark_Opti,(Risk_free/252))[[3]]
#Line 1.2: Markowitz traditional approach with copula var-cov glasso optimization problem
Mark_Opt.C_V=sr(log_returns_CW,w_Mark_Opti_glasso_copula,(Risk_free/252))[[3]]
#Line 1.3: Markowitz traditional approach with var-cov glasso optimization problem
Mark_Opt.G_V=sr(log_returns_CW,w_Mark_Opti_glasso,(Risk_free/252))[[3]]

#Graph #2: Markowitz traditional approach with forced restiriction long only
#Line 2.1: Markowitz traditional approach with forced restiriction long only (using S as var-cov)
Mark_Forced.S_V=sr(log_returns_CW,w_Mark_Forced,(Risk_free/252))[[3]]
#Line 2.2: Markowitz traditional approch with copula var-cov glasso forced resticction long only
Mark_Forced.C_V=sr(log_returns_CW,w_Mark_Forced_glasso_copula,(Risk_free/252))[[3]]
#Line 2.3: Markowitz traditional with var-cov glasso forced resticction long only
Mark_Forced.G_V=sr(log_returns_CW,w_Mark_Forced_glasso,(Risk_free/252))[[3]]

#Graph #3: Markowitz regression Ridge approach
#Line 3.1: Markowitz regression Ridge approach (with S as var-cov)
Ridge.S_V=sr(log_returns_CW,wRidge,(Risk_free/252))[[3]]
#Line 3.2: Markowitz regression Ridge approach with copula var-cov glasso
Ridge.C_V=sr(log_returns_CW,wRidge_glasso_copula,(Risk_free/252))[[3]]
#Line 3.3: Markowitz regression Ridge approach with var-cov glasso
Ridge.G_V=sr(log_returns_CW,wRidge_glasso,(Risk_free/252))[[3]]

#Graph 4: Markowitz regression Lasso approach
#Line 4.1: Markowitz regression Lasso approach (using S as var-cov)
Lasso.S_V=sr(log_returns_CW,wLasso,(Risk_free/252))[[3]]
#Line 4.2: Markowitz regression Lasso approach with copula var-cov glasso
Lasso.C_V=sr(log_returns_CW,wLasso_glasso_copula,(Risk_free/252))[[3]]
#Line 4.3: Markowitz regression LASSO approach with var-cov glasso
Lasso.G_V=sr(log_returns_CW,wLasso_glasso,(Risk_free/252))[[3]]
#Bar graph showing different portfolio volatilities
Models <- c(rep("Markowitz Optimization",3), 
            rep("Markowitz Forced",3), 
            rep("Ridge",3), 
            rep("Lasso",3))

# Three covariance and precision matrices
CovarianceMatrix <- rep(c("SS","GLASSO","Copula GLASSO"),4)
AverageVolatility <- c(Mark_Opt.S_V,Mark_Opt.G_V,Mark_Opt.C_V,Mark_Forced.S_V,Mark_Forced.G_V,Mark_Forced.C_V,Ridge.S_V,Ridge.G_V,Ridge.C_V,Lasso.S_V,Lasso.G_V,Lasso.C_V)
data <- data.frame(Models,CovarianceMatrix,AverageVolatility)
data$Models=factor(data$Models,levels=c("Markowitz Optimization","Markowitz Forced","Ridge","Lasso"))
data$CovarianceMatrix=factor(data$CovarianceMatrix,levels=c("SS","GLASSO","Copula GLASSO"))
# Plot the data
jpeg("AV_2008_G.jpg", width = 1081.5, height = 1215)
ggplot(data, aes(fill=CovarianceMatrix, y=AverageVolatility , x=Models)) + geom_bar(position="dodge", stat="identity")+scale_fill_hue(l=40, c=70)+ ggtitle("Portfolio Average Volatility")+theme(legend.position = c(0.8, 0.8),legend.title = element_text(size = 25),legend.text = element_text(size = 22),legend.key.size = unit(3,"line"),axis.text=element_text(size=18),axis.title=element_text(size=30,face="bold"),plot.title = element_text(size=26,face="bold"))
dev.off()
#####Model Validation Calmar Ratio#####
#We obtain the returns for each porfolio, and calculate the Calmar Ratio for each
#Graph #1: Markowitz traditional approach with optimization problem
#Line 1.1: Markowitz traditional approach with optimization problem (using S as var-cov)
Mark_Opt.S_CR=CalmarRatio(Return.portfolio(log_returns_CW,w_Mark_Opti),scale=252)
#Line 1.2: Markowitz traditional approach with copula var-cov glasso optimization problem
Mark_Opt.C_CR=CalmarRatio(Return.portfolio(log_returns_CW,w_Mark_Opti_glasso_copula),scale=252)
#Line 1.3: Markowitz traditional approach with var-cov glasso optimization problem
Mark_Opt.G_CR=CalmarRatio(Return.portfolio(log_returns_CW,w_Mark_Opti_glasso),scale=252)

#Graph #2: Markowitz traditional approach with forced restiriction long only
#Line 2.1: Markowitz traditional approach with forced restiriction long only (using S as var-cov)
Mark_Forced.S_CR=CalmarRatio(Return.portfolio(log_returns_CW,w_Mark_Forced),scale=252)
#Line 2.2: Markowitz traditional approch with copula var-cov glasso forced resticction long only
Mark_Forced.C_CR=CalmarRatio(Return.portfolio(log_returns_CW,w_Mark_Forced_glasso_copula),scale=252)
#Line 2.3: Markowitz traditional with var-cov glasso forced resticction long only
Mark_Forced.G_CR=CalmarRatio(Return.portfolio(log_returns_CW,w_Mark_Forced_glasso),scale=252)

#Graph #3: Markowitz regression Ridge approach
#Line 3.1: Markowitz regression Ridge approach (with S as var-cov)
Ridge.S_CR=CalmarRatio(Return.portfolio(log_returns_CW,wRidge),scale=252)
#Line 3.2: Markowitz regression Ridge approach with copula var-cov glasso
Ridge.C_CR=CalmarRatio(Return.portfolio(log_returns_CW,wRidge_glasso_copula),scale=252)
#Line 3.3: Markowitz regression Ridge approach with var-cov glasso
Ridge.G_CR=CalmarRatio(Return.portfolio(log_returns_CW,wRidge_glasso),scale=252)

#Graph 4: Markowitz regression Lasso approach
#Line 4.1: Markowitz regression Lasso approach (using S as var-cov)
Lasso.S_CR=CalmarRatio(Return.portfolio(log_returns_CW,wLasso),scale=252)
#Line 4.2: Markowitz regression Lasso approach with copula var-cov glasso
Lasso.C_CR=CalmarRatio(Return.portfolio(log_returns_CW,wLasso_glasso_copula),scale=252)
#Line 4.3: Markowitz regression LASSO approach with var-cov glasso
Lasso.G_CR=CalmarRatio(Return.portfolio(log_returns_CW,wLasso_glasso),scale=252)

#Bar graph showing different portfolio Calmar Ratios
Models <- c(rep("Markowitz Optimization",3), 
            rep("Markowitz Forced",3), 
            rep("Ridge",3), 
            rep("Lasso",3))

# Three covariance and precision matrices
CovarianceMatrix <- rep(c("SS","GLASSO","Copula GLASSO"),4)
CalmarRatio <- c(Mark_Opt.S_CR,Mark_Opt.G_CR,Mark_Opt.C_CR,Mark_Forced.S_CR,Mark_Forced.G_CR,Mark_Forced.C_CR,Ridge.S_CR,Ridge.G_CR,Ridge.C_CR,Lasso.S_CR,Lasso.G_CR,Lasso.C_CR)
data <- data.frame(Models,CovarianceMatrix,CalmarRatio)
data$Models=factor(data$Models,levels=c("Markowitz Optimization","Markowitz Forced","Ridge","Lasso"))
data$CovarianceMatrix=factor(data$CovarianceMatrix,levels=c("SS","GLASSO","Copula GLASSO"))
# Plot the data
jpeg("CR_2008_G.jpg", width = 1081.5, height = 1215)
ggplot(data, aes(fill=CovarianceMatrix, y=CalmarRatio , x=Models)) + geom_bar(position="dodge", stat="identity")+scale_fill_hue(l=40, c=70)+ ggtitle("Portfolio Calmar Ratio")+theme(legend.position = c(0.2, 0.85),legend.title = element_text(size = 25),legend.text = element_text(size = 22),legend.key.size = unit(3,"line"),axis.text=element_text(size=18),axis.title=element_text(size=30,face="bold"),plot.title = element_text(size=26,face="bold"))
dev.off()

#####Model Validation Maximum Drawdown#####
#We obtain the returns for each porfolio, and calculate the Maximum Drawdown for each
#Graph #1: Markowitz traditional approach with optimization problem
#Line 1.1: Markowitz traditional approach with optimization problem (using S as var-cov)
Mark_Opt.S_MD=maxDrawdown(Return.portfolio(log_returns_CW,w_Mark_Opti))
#Line 1.2: Markowitz traditional approach with copula var-cov glasso optimization problem
Mark_Opt.C_MD=maxDrawdown(Return.portfolio(log_returns_CW,w_Mark_Opti_glasso_copula))
#Line 1.3: Markowitz traditional approach with var-cov glasso optimization problem
Mark_Opt.G_MD=maxDrawdown(Return.portfolio(log_returns_CW,w_Mark_Opti_glasso))

#Graph #2: Markowitz traditional approach with forced restiriction long only
#Line 2.1: Markowitz traditional approach with forced restiriction long only (using S as var-cov)
Mark_Forced.S_MD=maxDrawdown(Return.portfolio(log_returns_CW,w_Mark_Forced))
#Line 2.2: Markowitz traditional approch with copula var-cov glasso forced resticction long only
Mark_Forced.C_MD=maxDrawdown(Return.portfolio(log_returns_CW,w_Mark_Forced_glasso_copula))
#Line 2.3: Markowitz traditional with var-cov glasso forced resticction long only
Mark_Forced.G_MD=maxDrawdown(Return.portfolio(log_returns_CW,w_Mark_Forced_glasso))

#Graph #3: Markowitz regression Ridge approach
#Line 3.1: Markowitz regression Ridge approach (with S as var-cov)
Ridge.S_MD=maxDrawdown(Return.portfolio(log_returns_CW,wRidge))
#Line 3.2: Markowitz regression Ridge approach with copula var-cov glasso
Ridge.C_MD=maxDrawdown(Return.portfolio(log_returns_CW,wRidge_glasso_copula))
#Line 3.3: Markowitz regression Ridge approach with var-cov glasso
Ridge.G_MD=maxDrawdown(Return.portfolio(log_returns_CW,wRidge_glasso))

#Graph 4: Markowitz regression Lasso approach
#Line 4.1: Markowitz regression Lasso approach (using S as var-cov)
Lasso.S_MD=maxDrawdown(Return.portfolio(log_returns_CW,wLasso))
#Line 4.2: Markowitz regression Lasso approach with copula var-cov glasso
Lasso.C_MD=maxDrawdown(Return.portfolio(log_returns_CW,wLasso_glasso_copula))

#Line 4.3: Markowitz regression LASSO approach with var-cov glasso
Lasso.G_MD=maxDrawdown(Return.portfolio(log_returns_CW,wLasso_glasso))

#Bar graph showing different portfolio Maximum Drawdown
Models <- c(rep("Markowitz Optimization",3), 
            rep("Markowitz Forced",3), 
            rep("Ridge",3), 
            rep("Lasso",3))

# Three covariance and precision matrices
CovarianceMatrix <- rep(c("SS","GLASSO","Copula GLASSO"),4)
MaxDrawdown <- c(Mark_Opt.S_MD,Mark_Opt.G_MD,Mark_Opt.C_MD,Mark_Forced.S_MD,Mark_Forced.G_MD,Mark_Forced.C_MD,Ridge.S_MD,Ridge.G_MD,Ridge.C_MD,Lasso.S_MD,Lasso.G_MD,Lasso.C_MD)
data <- data.frame(Models,CovarianceMatrix,MaxDrawdown)
data$Models=factor(data$Models,levels=c("Markowitz Optimization","Markowitz Forced","Ridge","Lasso"))
data$CovarianceMatrix=factor(data$CovarianceMatrix,levels=c("SS","GLASSO","Copula GLASSO"))
# Plot the data
jpeg("MD_2008_G.jpg", width = 1081.5, height = 1215)
ggplot(data, aes(fill=CovarianceMatrix, y=MaxDrawdown , x=Models)) + geom_bar(position="dodge", stat="identity")+scale_fill_hue(l=40, c=70)+ ggtitle("Portfolio Maximum Drawdown")+theme(legend.position = c(0.8, 0.8),legend.title = element_text(size = 25),legend.text = element_text(size = 22),legend.key.size = unit(3,"line"),axis.text=element_text(size=18),axis.title=element_text(size=30,face="bold"),plot.title = element_text(size=26,face="bold"))
dev.off()

######Model Validation Information Ratio####
#For Information Ratio validation, we need to search for two benchmark references
#1st Benchmark: S&P500
#2nd Benchmark: Both Markowitz portfolios calculated (Optimal and Forced)
#Comparison with S&P500
#We obtain the S&P500 returns for the out-of-sample period (last 252 days)
getSymbols("^GSPC", src = "yahoo", from='2008-01-01')
GSPC=GSPC[, 6]
size=1*nrow(GSPC)
brake=1*(size-252)
#Testing set
GSPC_CW=GSPC[(brake+1):size,]
log_returns_GSPC=diff(log(GSPC_CW))
log_returns_GSPC=log_returns_GSPC[-1]
#Function for Information Ratio
#Function: Information Ratio
#Description: The IR function returns a scalar representing the information ratio according with the inputed parameters, including the benchmark
#Inputs: market_log_ret: data that will be used for the estimation from the portfolio side
#portfolio: Portfolio to evaluate 
#benchmark_ret: The benchmark returns 

#Output: (scalar) The calculated information ratio using the benchmark inputed

ir=function(market_log_ret,portfolio,benchmark_ret){
  #for(i in 1:n){
  #  Rt[i]=t(portfolio)%*%as.matrix(log_ret[i,])
  #}
  Rt=Return.portfolio(market_log_ret,portfolio)
  excess=Rt-benchmark_ret
  SD=sd(excess)*sqrt(252)
  MU=mean(excess)*252
  IR=MU/SD
  list=list(IR,MU,SD)
  return (list)
}

#Bar graph showing portfolios information ratios vs. S&P500 and both Markowitz Optimization portfolios
#Graph #1: Markowitz traditional approach with optimization problem
#Line 1.1: Markowitz traditional approach with optimization problem (using S as var-cov)
Mark_Opt.S_IR_SP500=ir(log_returns_CW,w_Mark_Opti,log_returns_GSPC)[[1]]
Rt=Return.portfolio(log_returns_CW,w_Mark_Forced)
Mark_Opt.S_IR_MF=ir(log_returns_CW,w_Mark_Opti,Rt)[[1]]
#Line 1.2: Markowitz traditional approach with copula var-cov glasso optimization problem
Mark_Opt.C_IR_SP500=ir(log_returns_CW,w_Mark_Opti_glasso_copula,log_returns_GSPC)[[1]]
Rt=Return.portfolio(log_returns_CW,w_Mark_Forced)
Mark_Opt.C_IR_MF=ir(log_returns_CW,w_Mark_Opti_glasso_copula,Rt)[[1]]
#Line 1.3: Markowitz traditional approach with var-cov glasso optimization problem
Mark_Opt.G_IR_SP500=ir(log_returns_CW,w_Mark_Opti_glasso,log_returns_GSPC)[[1]]
Rt=Return.portfolio(log_returns_CW,w_Mark_Forced)
Mark_Opt.G_IR_MF=ir(log_returns_CW,w_Mark_Opti_glasso,Rt)[[1]]

#Graph #2: Markowitz traditional approach with forced restiriction long only
#Line 2.1: Markowitz traditional approach with forced restiriction long only (using S as var-cov)
Mark_Forced.S_IR_SP500=ir(log_returns_CW,w_Mark_Forced,log_returns_GSPC)[[1]]
Rt=Return.portfolio(log_returns_CW,w_Mark_Opti)
Mark_Forced.S_IR_MO=ir(log_returns_CW,w_Mark_Forced,Rt)[[1]]
#Line 2.2: Markowitz traditional approch with copula var-cov glasso forced resticction long only
Mark_Forced.C_IR_SP500=ir(log_returns_CW,w_Mark_Forced_glasso_copula,log_returns_GSPC)[[1]]
Rt=Return.portfolio(log_returns_CW,w_Mark_Opti)
Mark_Forced.C_IR_MO=ir(log_returns_CW,w_Mark_Forced_glasso_copula,Rt)[[1]]
#Line 2.3: Markowitz traditional with var-cov glasso forced resticction long only
Mark_Forced.G_IR_SP500=ir(log_returns_CW,w_Mark_Forced_glasso,log_returns_GSPC)[[1]]
Rt=Return.portfolio(log_returns_CW,w_Mark_Opti)
Mark_Forced.G_IR_MO=ir(log_returns_CW,w_Mark_Forced_glasso,Rt)[[1]]

#Graph #3: Markowitz regression Ridge approach
#Line 3.1: Markowitz regression Ridge approach (with S as var-cov)
Rt=Return.portfolio(log_returns_CW,w_Mark_Opti)
Ridge.S_IR_MO=ir(log_returns_CW,wRidge,Rt)[[1]]
Rt=Return.portfolio(log_returns_CW,w_Mark_Forced)
Ridge.S_IR_MF=ir(log_returns_CW,wRidge,Rt)[[1]]
Ridge.S_IR_SP500=ir(log_returns_CW,wRidge,log_returns_GSPC)[[1]]
#Line 3.2: Markowitz regression Ridge approach with copula var-cov glasso
Rt=Return.portfolio(log_returns_CW,w_Mark_Opti)
Ridge.C_IR_MO=ir(log_returns_CW,wRidge_glasso_copula,Rt)[[1]]
Rt=Return.portfolio(log_returns_CW,w_Mark_Forced)
Ridge.C_IR_MF=ir(log_returns_CW,wRidge_glasso_copula,Rt)[[1]]
Ridge.C_IR_SP500=ir(log_returns_CW,wRidge_glasso_copula,log_returns_GSPC)[[1]]
#Line 3.3: Markowitz regression Ridge approach with var-cov glasso
Rt=Return.portfolio(log_returns_CW,w_Mark_Opti)
Ridge.G_IR_MO=ir(log_returns_CW,wRidge_glasso,Rt)[[1]]
Rt=Return.portfolio(log_returns_CW,w_Mark_Forced)
Ridge.G_IR_MF=ir(log_returns_CW,wRidge_glasso,Rt)[[1]]
Ridge.G_IR_SP500=ir(log_returns_CW,wRidge_glasso,log_returns_GSPC)[[1]]

#Graph 4: Markowitz regression Lasso approach
#Line 4.1: Markowitz regression Lasso approach (using S as var-cov)
Rt=Return.portfolio(log_returns_CW,w_Mark_Opti)
Lasso.S_IR_MO=ir(log_returns_CW,wLasso,Rt)[[1]]
Rt=Return.portfolio(log_returns_CW,w_Mark_Forced)
Lasso.S_IR_MF=ir(log_returns_CW,wLasso,Rt)[[1]]
Lasso.S_IR_SP500=ir(log_returns_CW,wLasso,log_returns_GSPC)[[1]]
#Line 4.2: Markowitz regression Lasso approach with copula var-cov glasso
Rt=Return.portfolio(log_returns_CW,w_Mark_Opti)
Lasso.C_IR_MO=ir(log_returns_CW,wLasso_glasso_copula,Rt)[[1]]
Rt=Return.portfolio(log_returns_CW,w_Mark_Forced)
Lasso.C_IR_MF=ir(log_returns_CW,wLasso_glasso_copula,Rt)[[1]]
Lasso.C_IR_SP500=ir(log_returns_CW,wLasso_glasso_copula,log_returns_GSPC)[[1]]
#Line 4.3: Markowitz regression LASSO approach with var-cov glasso
Rt=Return.portfolio(log_returns_CW,w_Mark_Opti)
Lasso.G_IR_MO=ir(log_returns_CW,wLasso_glasso,Rt)[[1]]
Rt=Return.portfolio(log_returns_CW,w_Mark_Forced)
Lasso.G_IR_MF=ir(log_returns_CW,wLasso_glasso,Rt)[[1]]
Lasso.G_IR_SP500=ir(log_returns_CW,wLasso_glasso,log_returns_GSPC)[[1]]

#Bar graph showing information ratio for different models (Benchmark= S&P500)
Models <- c(rep("Markowitz Optimization",3), 
            rep("Markowitz Forced",3), 
            rep("Ridge",3), 
            rep("Lasso",3))

# Three covariance and precision matrices
CovarianceMatrix <- rep(c("SS","GLASSO","Copula GLASSO"),4)
InformationRatio <- c(Mark_Opt.S_IR_SP500,Mark_Opt.G_IR_SP500,Mark_Opt.C_IR_SP500,Mark_Forced.S_IR_SP500,Mark_Forced.G_IR_SP500,Mark_Forced.C_IR_SP500,Ridge.S_IR_SP500,Ridge.G_IR_SP500,Ridge.C_IR_SP500,Lasso.S_IR_SP500,Lasso.G_IR_SP500,Lasso.C_IR_SP500)
data <- data.frame(Models,CovarianceMatrix,InformationRatio)
data$Models=factor(data$Models,levels=c("Markowitz Optimization","Markowitz Forced","Ridge","Lasso"))
data$CovarianceMatrix=factor(data$CovarianceMatrix,levels=c("SS","GLASSO","Copula GLASSO"))
# Plot the data
jpeg("IR_S&P500_2008_G.jpg", width = 1081.5, height = 1215)
ggplot(data, aes(fill=CovarianceMatrix, y=InformationRatio , x=Models)) + geom_bar(position="dodge", stat="identity")+scale_fill_hue(l=40, c=70)+labs(title="Portfolio Information Ratio",subtitle="Benchmark = S&P500")+theme(legend.position = c(0.2, 0.85),legend.title = element_text(size = 25),legend.text = element_text(size = 22),legend.key.size = unit(3,"line"),axis.text=element_text(size=18),axis.title=element_text(size=30,face="bold"),plot.title = element_text(size=26,face="bold"),plot.subtitle = element_text(size=22))
dev.off()

#Bar graph showing information ratio for different models (Benchmark= Mark Opti)
Models <- c(rep("Markowitz Forced",3),rep("Ridge",3), 
            rep("Lasso",3))

# Three covariance and precision matrices
CovarianceMatrix <- rep(c("SS","GLASSO","Copula GLASSO"),3)
InformationRatio <- c(Mark_Forced.S_IR_MO,Mark_Forced.G_IR_MO,Mark_Forced.C_IR_MO,Ridge.S_IR_MO,Ridge.G_IR_MO,Ridge.C_IR_MO,Lasso.S_IR_MO,Lasso.G_IR_MO,Lasso.C_IR_MO)
data <- data.frame(Models,CovarianceMatrix,InformationRatio)
data$Models=factor(data$Models,levels=c("Markowitz Optimization","Markowitz Forced","Ridge","Lasso"))
data$CovarianceMatrix=factor(data$CovarianceMatrix,levels=c("SS","GLASSO","Copula GLASSO"))
# Plot the data
jpeg("IR_MarkOpt_2008_G.jpg", width = 1081.5, height = 1215)
ggplot(data, aes(fill=CovarianceMatrix, y=InformationRatio , x=Models)) + geom_bar(position="dodge", stat="identity")+scale_fill_hue(l=40, c=70)+labs(title="Portfolio Information Ratio",subtitle="Benchmark = Markowitz Optimization w/ S")+theme(legend.position = c(0.2, 0.85),legend.title = element_text(size = 25),legend.text = element_text(size = 22),legend.key.size = unit(3,"line"),axis.text=element_text(size=18),axis.title=element_text(size=30,face="bold"),plot.title = element_text(size=26,face="bold"),plot.subtitle = element_text(size=22))
dev.off()

#Bar graph showing information ratio for different models (Benchmark= Mark Forced)
Models <- c(rep("Markowitz Optimization",3),rep("Ridge",3), 
            rep("Lasso",3))
# Three covariance and precision matrices
CovarianceMatrix <- rep(c("SS","GLASSO","Copula GLASSO"),3)
InformationRatio <- c(Mark_Opt.S_IR_MF,Mark_Opt.G_IR_MF,Mark_Opt.C_IR_MF,Ridge.S_IR_MF,Ridge.G_IR_MF,Ridge.C_IR_MF,Lasso.S_IR_MF,Lasso.G_IR_MF,Lasso.C_IR_MF)
data <- data.frame(Models,CovarianceMatrix,InformationRatio)
data$Models=factor(data$Models,levels=c("Markowitz Optimization","Markowitz Forced","Ridge","Lasso"))
data$CovarianceMatrix=factor(data$CovarianceMatrix,levels=c("SS","GLASSO","Copula GLASSO"))
# Plot the data
jpeg("IR_MarkForced_2008_G.jpg", width = 1081.5, height = 1215)
ggplot(data, aes(fill=CovarianceMatrix, y=InformationRatio , x=Models)) + geom_bar(position="dodge", stat="identity")+scale_fill_hue(l=40, c=70)+labs(title="Portfolio Information Ratio",subtitle="Benchmark = Markowitz Forced w/ S")+theme(legend.position = c(0.2, 0.85),legend.title = element_text(size = 25),legend.text = element_text(size = 22),legend.key.size = unit(3,"line"),axis.text=element_text(size=18),axis.title=element_text(size=30,face="bold"),plot.title = element_text(size=26,face="bold"),plot.subtitle = element_text(size=22))
dev.off()

#PARA ENTREGAR EL CÓDIGO, BORRAR LOS 2008 DE LOS GRAFICOS, MEJORAR ALGUNAS DESCRIPCIONES, VERIFICAR LO QUE SE DECIA DE UN INDICE LHX


