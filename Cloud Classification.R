##################################################################################################
########## Code developed based on the course by Dr. Peter Bubenik at University of Florida ######
##################################################################################################

rm(list=ls())

library(png)
library(colorspace)

library(rlist)

library(TDA)

library(deldir) 
library("Matrix") # package for sparse matrices
#library("SparseM")
library("e1071")

library("FNN")


library(neuralnet)

library(MASS)


#################################
#################################
#################################

# Euclidean distance between vectors
euclidean.distance <- function(u, v) sqrt(sum((u - v) ^ 2))

# Sample points from an annulus
#sample.annulus <- function(num.pts, inner.radius, outer.radius){
#  theta <- runif(num.pts) * 2 * pi
#  radius <- sqrt(runif(num.pts, inner.radius^2, outer.radius^2))
#  x <- radius * cos(theta)
#  y <- radius * sin(theta)
#  cbind(x,y)
#}

# Plot the Voronoi cells and dual and Delaunay complex
plot.delaunay <- function(X){
  DelVor <- deldir(X[,1], X[,2], suppressMsge = TRUE)
  # Voronoi cells:
  plot(DelVor, pch=20, cmpnt_col=c("black","red","blue"), wlines= ("tess"))
  # Voronoi cells and their dual (the Delaunay complex):
  plot(DelVor, pch=20, cmpnt_col=c("black","red","blue"), wlines= ("both"))
  # Delaunay complex:
  plot(DelVor, pch=20, cmpnt_col=c("black","red","blue"), wlines= ("triang"))
}

# Plot the Vietoris-Rips complex up to some filtration value
#plot.rips <- function(X,max.filtration){
#  plot(X, pch=20, col="blue", asp=1)
#  num.pts <- dim(X)[1]
#  for(i in 1:num.pts)
#    for(j in 1:num.pts)
#      if (euclidean.distance(X[i,],X[j,]) < max.filtration)
#        lines(rbind(X[i,],X[j,]))
#}

# Plot representative cycles for Delaunay complex
plot.delaunay.cycle <- function(X){
  PH.output <- alphaComplexDiag(X, maxdimension = 1, library = c("GUDHI", "Dionysus"), 
                                location = TRUE)
  PD <- PH.output[["diagram"]]
  ones <- which(PD[, 1] == 1)
  persistence <- PD[ones,3] - PD[ones,2]
  cycles <- PH.output[["cycleLocation"]][ones[order(persistence)]]
  for (i in 1:length(cycles)){
    plot(X, pch=20, col="blue", asp=1)
    for (j in 1:dim(cycles[[i]])[1])
      lines(cycles[[i]][j,,])
  }
}

### Plot representative cycles for Vietoris-Rips complex
#plot.rips.cycle <- function(X){
#  PH.output <- ripsDiag(X, maxdimension = 1, maxscale = max.filtration, 
#                        library = c("GUDHI", "Dionysus"), location = TRUE)
#  PD <- PH.output[["diagram"]]
#  ones <- which(PD[, 1] == 1)
#  persistence <- PD[ones,3] - PD[ones,2]
#  cycles <- PH.output[["cycleLocation"]][ones[order(persistence)]]
#  for (i in 1:length(cycles)){
#    plot(X, pch=20, col="blue", asp=1)
#    for (j in 1:dim(cycles[[i]])[1])
#      lines(cycles[[i]][j,,])
#  }
#}

# Death Vector
death.vector <- function(PD){
  zeroes <- which(PD[, 1] == 0)
  PD.0 <- PD[zeroes,2:3]
  dv <- vector()
  if ((min(PD.0[,"Birth"]) == 0) && (max(PD.0[,"Birth"]) == 0))
    dv <- sort(PD.0[,2], decreasing=TRUE)
  return(dv)
}

# Plot Persistence Landscape
plot.landscape <- function(PL,t.vals){
  plot(t.vals,PL[1,],type="l",ylab="Persistence",xlab="Parameter values",col=1,ylim=c(min(PL),max(PL)))
  for(i in 2:dim(PL)[1])
    lines(t.vals,PL[i,],type="l",col=i)
}

# Matrix of death vectors from a list of persistence diagrams
death.vector.matrix <- function(PD.list){
  num.pts <- length(which(PD.list[[1]][,1] == 0))
  DVM <- matrix(0L, nrow = length(PD.list), ncol = num.pts - 1)
  for (c in 1 : length(PD.list))
    DVM[c,] <- death.vector(PD.list[[c]])[-1]
  return(DVM)
}

# Matrix of persistence landscape row vectors from list of persistence landscapes
landscape.matrix.from.list <- function(PL.list){
  n <- length(PL.list)
  m <- ncol(PL.list[[1]])
  max.depth <- integer(n)
  for (i in 1:n)
    max.depth[i] <- nrow(PL.list[[i]])
  K <- max(max.depth)
  PL.matrix <- Matrix(0, nrow = n, ncol = m*K, sparse = TRUE)
  for (i in 1:n)
    for (j in 1:max.depth[i])
      PL.matrix[i,(1+(j-1)*m):(j*m)] <- PL.list[[i]][j,]
  return(PL.matrix)
}

# Convert a vector to a persistence landscape
landscape.from.vector <- function(PL.vector, t.vals){
  m <- length(t.vals)
  K <- length(PL.vector)/m
  PL <- Matrix(0, nrow = K, ncol=m, sparse = TRUE)
  for (i in 1:K){
    PL[i,1:m] <- PL.vector[(1+(i-1)*m):(i*m)]
  }
  return(PL)
}

# Take difference of vectors of potentially different lengths
difference.vectors <-function(vector.1,vector.2){
  length.1 <- length(vector.1)
  length.2 <- length(vector.2)
  difference.vector = numeric(max(length.1,length.2))
  difference.vector = as(difference.vector, "sparseVector")
  difference.vector[1:length.1] = difference.vector[1:length.1] + vector.1
  difference.vector[1:length.2] = difference.vector[1:length.2] - vector.2
}

# Permutation test for two matrices consisting of row vectors
permutation.test <- function(M1 ,M2, num.repeats = 10000){
  # append zeros if necessary so that the matrices have the same number of columns
  num.columns <- max(ncol(M1),ncol(M2))
  M1 <- cbind(M1, Matrix(0,nrow=nrow(M1),ncol=num.columns-ncol(M1)))
  M2 <- cbind(M2, Matrix(0,nrow=nrow(M2),ncol=num.columns-ncol(M2)))
  t.obs <- euclidean.distance(colMeans(M1),colMeans(M2))
  k <- dim(M1)[1]
  M <- rbind(M1,M2)
  n <- dim(M)[1]
  count <- 0
  for (i in 1:num.repeats){
    permutation <- sample(1:n)
    t <- euclidean.distance(colMeans(M[permutation[1:k],]),colMeans(M[permutation[(k+1):n],]))
    if (t >= t.obs)
      count <- count + 1
  }
  return(count/num.repeats)
}

sample.digital.image <- function(gray.scale.matrix, num.pts=100){
  V <- as.vector(t(gray.scale.matrix))
  W <- integer(length=length(V))
  W[1] <- V[1]
  for (i in 2:length(V))
    W[i] <- W[i-1] + V[i]
  X <- matrix(0,nrow=num.pts,ncol=2)
  for (i in 1:num.pts){
    r <- runif(1)*W[length(W)]
    A <- W<r
    entry <- sum(A)+1
    b <- entry %/% 390
    a <- entry %% 294
    X[i,1] <- (a + runif(1))/391
    X[i,2] <- 1 - (b + runif(1))/295
  }
  return(X)
}


#################################
#################################
#################################


###################################################
### LOADING IMAGES IN AND PREPROCESSING ############
###################################################



dir.string <- "C:/Users/DELL/Desktop/Clouds TDA/data/"

#Clouds.A - Cirrus
#Clouds.B - Cumulus
#Clouds.C - Altocumulus 

Ci.names <- Cu.names <- Ac.names <- as.character(1:40)

Clouds.A <- matrix(0, ncol = length(Ci.names), nrow = 390 * 294)
Clouds.B <- matrix(0, ncol = length(Cu.names), nrow = 390 * 294)
Clouds.C <- matrix(0, ncol = length(Ac.names), nrow = 390 * 294)

for (ii in 1:length(Ci.names)) {
  x <- readPNG(paste(dir.string, "Ci/", Ci.names[ii], ".png", sep = ""))
  
  y <- rgb(x[,,1], x[,,2], x[,,3])
  yg <- desaturate(y)
  y_red <- col2rgb(y)[1, ] #1 - red, 2 - green, 3 - blue
  y_green <-col2rgb(y)[2, ]
  y_blue <- col2rgb(y)[3, ]
  
  pca.col <- prcomp(t(col2rgb(y)), rank = 1)
  y_PCA <- pca.col$x
  
  dim(y) <- dim(yg) <- dim(y_red) <- dim(y_green) <- dim(y_blue) <- dim(y_PCA) <- dim(x)[1:2]
  
  y_PCA <- y_PCA + max(-min(y_PCA), 0)
  
  y_PCA <- round(y_PCA * (255 / max(y_PCA)))
  
  yn <- y_PCA
  
  yn <- yn[1:294, 1:390]
  
  mean <- mean(y_PCA)
  
  yn_2 <- yn
  
  for (i in 1:nrow(yn_2)) {
    for (j in 1:ncol(yn_2)) {
      if (y_PCA[i,j] < 1.0 * mean)
      {
        yn_2[i,j] <- 0
      }
    }
  }
  
  if (ii < 5) {
    image(1 - yn_2, useRaster=TRUE, axes=FALSE)
  }
  
  yn_2 <- matrix(yn_2, ncol = 1)
  
  Clouds.A[,ii] <- yn_2
  
}



for (ii in 1:length(Cu.names)) {
  x <- readPNG(paste(dir.string, "Cu/", Cu.names[ii], ".png", sep = ""))
  
  x <- readPNG(paste(dir.string, "Cu/Cu-N017.png", sep = ""))
  y <- rgb(x[,,1], x[,,2], x[,,3])
  yg <- desaturate(y)
  y_red <- col2rgb(y)[1, ] #1 - red, 2 - green, 3 - blue
  y_green <-col2rgb(y)[2, ]
  y_blue <- col2rgb(y)[3, ]
  
  pca.col <- prcomp(t(col2rgb(y)), rank = 1)
  y_PCA <- pca.col$x
  
  dim(y) <- dim(yg) <- dim(y_red) <- dim(y_green) <- dim(y_blue) <- dim(y_PCA) <- dim(x)[1:2]
  
  y_PCA <- y_PCA + max(-min(y_PCA), 0)
  
  y_PCA <- round(y_PCA * (255 / max(y_PCA)))
  
  yn <- y_PCA
  
  #image(1 - yn, useRaster=TRUE, axes=FALSE, col = gray.colors(12, rev = TRUE))
  
  yn <- yn[1:294, 1:390]
  
  mean <- mean(y_PCA)
  
  yn_2 <- yn
  
  
  for (i in 1:nrow(yn_2)) {
    for (j in 1:ncol(yn_2)) {
      if (y_PCA[i,j] < 1.0 * mean)
      {
        yn_2[i,j] <- 0
      }
    }
  }
  
  if (ii < 5) {
    image(1 - yn_2, useRaster=TRUE, axes=FALSE, col = gray.colors(12, rev = TRUE))
  }
  
  yn_2 <- matrix(yn_2, ncol = 1)
  
  Clouds.B[,ii] <- yn_2
  
}



for (ii in 1:length(Ac.names)) {
  x <- readPNG(paste(dir.string, "Ac/", Ac.names[ii], ".png", sep = ""))
  
  y <- rgb(x[,,1], x[,,2], x[,,3])
  yg <- desaturate(y)
  y_red <- col2rgb(y)[1, ] #1 - red, 2 - green, 3 - blue
  y_green <-col2rgb(y)[2, ]
  y_blue <- col2rgb(y)[3, ]
  
  pca.col <- prcomp(t(col2rgb(y)), rank = 1)
  y_PCA <- pca.col$x
  
  dim(y) <- dim(yg) <- dim(y_red) <- dim(y_green) <- dim(y_blue) <- dim(y_PCA) <- dim(x)[1:2]
  
  y_PCA <- y_PCA + max(-min(y_PCA), 0)
  
  y_PCA <- round(y_PCA * (255 / max(y_PCA)))
  
  yn <- y_PCA
  
  yn <- yn[1:294, 1:390]
  
  mean <- mean(y_PCA)
  
  yn_2 <- yn
  
  
  for (i in 1:nrow(yn_2)) {
    for (j in 1:ncol(yn_2)) {
      if (y_PCA[i,j] < 1.0 * mean)
      {
        yn_2[i,j] <- 0
      }
    }
  }
  
  if (ii < 5) {
    image(1 - yn_2, useRaster=TRUE, axes=FALSE)
  }
  
  yn_2 <- matrix(yn_2, ncol = 1)
  
  Clouds.C[,ii] <- yn_2
  
}



##########################################################################################
############### CONSTRUCTING PERSISTENT HOMOLOGY - FIRST METHOD ##########################
##########################################################################################




# First method: use sublevel persistent homology on a cubical complex using negative pixel values
min.t <- -255
max.t <- 0

t.steps <- 200
t.vals <- seq(min.t,max.t,(max.t-min.t)/t.steps)

num.repeats <- ncol(Clouds.A)

cloud_bitmap <- Clouds.A[,1]
V <- as.numeric(cloud_bitmap)

pixels <- matrix(0,nrow=length(V),2)

counter <- 1
for (i in 1:294) {
  for (j in 1:390) {
    pixels[counter,] <- c(i, j)
    counter <- counter + 1
  }
}

# First class of samples
PD.list <- vector("list",num.repeats)
for (c in 1 : num.repeats){
  cloud_bitmap <- Clouds.A[,c]
  V <- as.numeric(cloud_bitmap)
  M <- matrix(as.numeric(cloud_bitmap),nrow=390,ncol=294,byrow=TRUE)
  PH.output <- gridDiag(X = pixels, FUNvalues = -M, sublevel = TRUE)
  PD.list[[c]] <- PH.output[["diagram"]]
}

PL.list.A.0 <- vector("list",num.repeats)
for (c in 1 : num.repeats)
  PL.list.A.0[[c]] <- t(landscape(PD.list[[c]],dimension=0,KK=1:100,tseq=t.vals))
PL.matrix.A.0 <- landscape.matrix.from.list(PL.list.A.0)
average.PL.vector.A.0 <- colMeans(PL.matrix.A.0, sparseResult = TRUE)
average.PL.A.0 <- landscape.from.vector(average.PL.vector.A.0,t.vals)
plot.landscape(average.PL.A.0,t.vals)

#PL.mat <- matrix(PL.matrix.C.0[5,], nrow = 100)
#plot.landscape(PL.mat, t.vals)

#plot(PL.matrix.A.0[3,], type = "l")
#plot(average.PL.A.0, type = "l")

PL.list.A.1 <- vector("list",num.repeats)
for (c in 1 : num.repeats)
  PL.list.A.1[[c]] <- t(landscape(PD.list[[c]],dimension=1,KK=1:100,tseq=t.vals))
PL.matrix.A.1 <- landscape.matrix.from.list(PL.list.A.1)
average.PL.vector.A.1 <- colMeans(PL.matrix.A.1, sparseResult = TRUE)
average.PL.A.1 <- landscape.from.vector(average.PL.vector.A.1,t.vals)
plot.landscape(average.PL.A.1,t.vals)

# Second class of samples

num.repeats <- ncol(Clouds.B)

PD.list.2 <- vector("list",num.repeats)
for (c in 1 : num.repeats){
  cloud_bitmap <- Clouds.B[,c]
  V <- as.numeric(cloud_bitmap)
  M <- matrix(as.numeric(cloud_bitmap),nrow=390,ncol=294,byrow=TRUE)
  PH.output <- gridDiag(X = pixels, FUNvalues = -M, sublevel = TRUE)
  PD.list.2[[c]] <- PH.output[["diagram"]]
}

PL.list.B.0 <- vector("list",num.repeats)
for (c in 1 : num.repeats)
  PL.list.B.0[[c]] <- t(landscape(PD.list.2[[c]],dimension=0,KK=1:100,tseq=t.vals))
PL.matrix.B.0 <- landscape.matrix.from.list(PL.list.B.0)
average.PL.vector.B.0 <- colMeans(PL.matrix.B.0, sparseResult = TRUE)
average.PL.B.0 <- landscape.from.vector(average.PL.vector.B.0,t.vals)
plot.landscape(average.PL.B.0,t.vals)

PL.list.B.1 <- vector("list",num.repeats)
for (c in 1 : num.repeats)
  PL.list.B.1[[c]] <- t(landscape(PD.list.2[[c]],dimension=1,KK=1:100,tseq=t.vals))
PL.matrix.B.1 <- landscape.matrix.from.list(PL.list.B.1)
average.PL.vector.B.1 <- colMeans(PL.matrix.B.1, sparseResult = TRUE)
average.PL.B.1 <- landscape.from.vector(average.PL.vector.B.1,t.vals)
plot.landscape(average.PL.B.1,t.vals)



# Third class of samples

num.repeats <- ncol(Clouds.C)

PD.list.3 <- vector("list",num.repeats)
for (c in 1 : num.repeats){
  cloud_bitmap <- Clouds.C[,c]
  V <- as.numeric(cloud_bitmap)
  M <- matrix(as.numeric(cloud_bitmap),nrow=390,ncol=294,byrow=TRUE)
  PH.output <- gridDiag(X = pixels, FUNvalues = -M, sublevel = TRUE)
  PD.list.3[[c]] <- PH.output[["diagram"]]
}

PL.list.C.0 <- vector("list",num.repeats)
for (c in 1 : num.repeats)
  PL.list.C.0[[c]] <- t(landscape(PD.list.3[[c]],dimension=0,KK=1:100,tseq=t.vals))
PL.matrix.C.0 <- landscape.matrix.from.list(PL.list.C.0)
average.PL.vector.C.0 <- colMeans(PL.matrix.C.0, sparseResult = TRUE)
average.PL.C.0 <- landscape.from.vector(average.PL.vector.C.0,t.vals)
plot.landscape(average.PL.C.0,t.vals)

PL.list.C.1 <- vector("list",num.repeats)
for (c in 1 : num.repeats)
  PL.list.C.1[[c]] <- t(landscape(PD.list.3[[c]],dimension=1,KK=1:100,tseq=t.vals))
PL.matrix.C.1 <- landscape.matrix.from.list(PL.list.C.1)
average.PL.vector.C.1 <- colMeans(PL.matrix.C.1, sparseResult = TRUE)
average.PL.C.1 <- landscape.from.vector(average.PL.vector.C.1,t.vals)
plot.landscape(average.PL.C.1,t.vals)



# The difference in death vectors and persistence landscapes
difference.average.PL.vector.0 <- difference.vectors(average.PL.vector.A.0,average.PL.vector.B.0)
difference.average.PL.0 <- landscape.from.vector(difference.average.PL.vector.0,t.vals)
plot.landscape(difference.average.PL.0,t.vals)
difference.average.PL.vector.1 <- difference.vectors(average.PL.vector.A.1,average.PL.vector.B.1)
difference.average.PL.1 <- landscape.from.vector(difference.average.PL.vector.1,t.vals)
plot.landscape(difference.average.PL.1,t.vals)

# p values for differences in the average landscapes
permutation.test(PL.matrix.A.0, PL.matrix.B.0, num.repeats = 1000)
permutation.test(PL.matrix.A.1, PL.matrix.B.1, num.repeats = 1000)

permutation.test(PL.matrix.A.0, PL.matrix.C.0, num.repeats = 1000)
permutation.test(PL.matrix.A.1, PL.matrix.C.1, num.repeats = 1000)

permutation.test(PL.matrix.B.0, PL.matrix.C.0, num.repeats = 1000)
permutation.test(PL.matrix.B.1, PL.matrix.C.1, num.repeats = 1000)

# Assemble the data
data.labels <- c(rep(1,nrow(PL.matrix.A.1)), rep(2,nrow(PL.matrix.B.1)), rep(3,nrow(PL.matrix.C.1)))
PL.vectors.0 <- rbind(PL.matrix.A.0,PL.matrix.B.0, PL.matrix.C.0)
PL.vectors.1 <- rbind(PL.matrix.A.1,PL.matrix.B.1, PL.matrix.C.1)


#data.labels <- c(rep(1,nrow(PL.matrix.A.1)), rep(2,nrow(PL.matrix.B.1)))
#PL.vectors.0 <- rbind(PL.matrix.A.0,PL.matrix.B.0)
#PL.vectors.1 <- rbind(PL.matrix.A.1,PL.matrix.B.1)


# SAVING - BLUE CHANNEL ------------------------------
#save(data.labels, file = "DataLabels_M1.RData")
#save(PL.vectors.0, file = "PLVectors_0_M1.RData")
#save(PL.vectors.1, file = "PLVectors_1_M1.RData")
# -------------------------------------

# SAVING - PCA ------------------------------
#save(data.labels, file = "DataLabels_PCA_M1.RData")
#save(PL.vectors.0, file = "PLVectors_PCA_0_M1.RData")
#save(PL.vectors.1, file = "PLVectors_PCA_1_M1.RData")
# -------------------------------------


# LOADING IN - Blue channel ----------------------------
# load("DataLabels_M1.RData")
# load("PLVectors_0_M1.RData")
# load("PLVectors_1_M1.RData")
#--------------------------------------


# LOADING IN - PCA ----------------------------
load("DataLabels_PCA_M1.RData")
load("PLVectors_PCA_0_M1.RData")
load("PLVectors_PCA_1_M1.RData")
#--------------------------------------



###############################################################################################
#################### ASSESMENT OF DIFFERENT METHODS USING CROSS VALIDATION ####################
###############################################################################################

# TO SEE THE RESULTS FROM THE NUERAL NET, UNCOMMENT THE RESPECTIVE SECTION 
# AND COMMENT OUT THE SVM SECTION


pca.0 <- prcomp(PL.vectors.0,rank=5)


set.seed(1)

K <- 10

#Data <- PL.vectors.0

Data.0 <- PL.vectors.0
Data.1 <- PL.vectors.1

labels <- data.labels

mean.error <- vector(length = 10)


for (jj in 1:length(mean.error)) {
  
  
  randOrder = sample(1:nrow(Data.0), nrow(Data.0), replace=FALSE)
  
  kGroups = list()
  for (k in 1 : K) {
    kGroups[[k]] = ((k-1)*nrow(Data.0)/10 + 1) : (k*nrow(Data.0)/10)
  }
  
  
  
  #errorMat = matrix(NA, K, length(param.vec))
  
  errorVec <- vector(length = K)
  for (k in 1 : K) {
    
    ## Split the data into training/testing
    testIndex = randOrder[kGroups[[k]]]
    
    #trainData = Data[-testIndex,]
    #testData = Data[testIndex,]
    
    trainData.0 = Data.0[-testIndex,]
    testData.0 = Data.0[testIndex,]
    
    trainData.1 = Data.1[-testIndex,]
    testData.1 = Data.1[testIndex,]
    
    
    trainLabels <- labels[-testIndex]
    testLabels <- labels[testIndex]
    
    
    # ------------------ ENSEMBLE METHOD USING SVM - VOTING SCHEME -----------------------

    votes <- matrix(0, nrow = nrow(testData.0), ncol = 3)

    pairs <- matrix(c(1,2, 1,3, 2,3), ncol = 2, byrow = TRUE)
    for (i in 1:3) {

      q <- pairs[i,1] # POSITIVE
      r <- pairs[i,2] # NEGATIVE

      s <- 4 - i # THE CLASS LEFT OUT

      trainData_q_r.0 <- trainData.0[which(trainLabels != s),]

      trainData_q_r.1 <- trainData.1[which(trainLabels != s),]

      trainLabels_q_r <- trainLabels[which(trainLabels != s)]




      model.0 <- svm(trainData_q_r.0, trainLabels_q_r, scale=FALSE,type="C-classification",kernel="linear", cost=1e-2,cross=0)
      pred.0 <- predict(model.0, testData.0, decision.values = TRUE)

      pred.0 <- attr(pred.0, "decision.values")

      model.1 <- svm(trainData_q_r.1, trainLabels_q_r, scale=FALSE,type="C-classification",kernel="linear", cost=1e-2,cross=0)
      pred.1 <- predict(model.1, testData.1, decision.values = TRUE)

      pred.1 <- attr(pred.1, "decision.values")

      # HOMOLOGY IN DEGREE 0
      #sum.pred <- pred.0

      # HOMOLOGY IN DEGREE 1
      #sum.pred <- pred.1

      # ENSEMBLE METHOD
      sum.pred <- 0.55 * pred.0 + 0.45 * pred.1


      for (hh in 1:length(sum.pred)) {
        if (sum.pred[hh] >= 0) {
          votes[hh, q] <- votes[hh, q] + abs(sum.pred[hh])
        }
        else {
          votes[hh, r] <- votes[hh, r] + abs(sum.pred[hh])
        }
      }
    }

    pred <- vector(length = nrow(votes))

    for (hh in 1:length(pred)) {
      pred[hh] <- which.max(votes[hh,])
    }

    
    
    # ------------------- NEURAL NET --------------------

    # trainDataNet <- data.frame(data.labels[-testIndex], pca.0$x[-testIndex,])
    # 
    # testDataNet <- data.frame(data.labels[testIndex], pca.0$x[testIndex,])
    # 
    # 
    # names(trainDataNet)[1] <- c("label")
    # 
    # names(testDataNet)[1] <- c("label")
    # 
    # model.net <- neuralnet(as.factor(label) ~ ., data = trainDataNet, hidden = 4, err.fct = "ce", threshold = 1e-2, stepmax = 1e6, linear.output = FALSE)
    # 
    # out <- compute(model.net, testDataNet[,2:ncol(testDataNet)])
    # 
    # pred.table <- round(out$net.result)
    # 
    # pred <- vector(length = nrow(pred.table))
    # for (ff in 1:nrow(pred.table)) {
    # 
    #   pred[ff] <- which.max(pred.table[ff,])
    # }

    #######################################################################
    errorVec[k] <- sum(pred != testLabels) / length(testLabels)
    #######################################################################
    
  }
  
  mean.error[jj] <- mean(errorVec)
  
}
mean(mean.error)



##########################################################################################
############### CONSTRUCTING PERSISTENT HOMOLOGY - SECOND METHOD ##########################
##########################################################################################

# NOTE: THE CODE BELOW WAS USED ONLY IN THE EARLY STAGE TO COMPARE THE PERFORMANCE OF
# BOTH METHODS FOR CONSTRUCTING PERSISTENT HOMOLOGY. SINCE THE METHOD BELOW YIELDED WORSE
# PRELIMINARY RESULTS ONLY THE METHOD ABOVE WAS UTILIZED FOR FURTHER STEPS IN THE PROJECT.



# Second method: use persistent homology of Delaunay complex on sampled points
min.t <- 0
max.t <- 0.15
t.vals <- seq(min.t,max.t,(max.t-min.t)/t.steps)

num.pts <- 5000

# First class of samples
num.repeats <- ncol(Clouds.A)

PD.list <- vector("list",num.repeats)
for (c in 1 : num.repeats){
  cloud_bitmap <- Clouds.A[,c]
  V <- as.numeric(cloud_bitmap)
  M <- matrix(as.numeric(cloud_bitmap),nrow=390,ncol=294,byrow=TRUE)
  X <- sample.digital.image(M,num.pts)
  
  X.max <- max(X[,1])
  for (ff in 1:nrow(X)) {
    if (X[ff, 1] < 0) {
      X[ff, 1] <- X.max + 1e-3
    }
  }
  
  PH.output <- alphaComplexDiag(X)
  PD.list[[c]] <- PH.output[["diagram"]]
  PD.list[[c]][,2:3] <- sqrt(PD.list[[c]][,2:3])
}

DV.matrix <- death.vector.matrix(PD.list)
average.DV <- colMeans(DV.matrix)
plot(average.DV, type="l", col="blue", ylab = "Persistence")

PL.list <- vector("list",num.repeats)
for (c in 1 : num.repeats)
  PL.list[[c]] <- t(landscape(PD.list[[c]],dimension=1,KK=1:100,tseq=t.vals))
PL.matrix <- landscape.matrix.from.list(PL.list)
average.PL.vector <- colMeans(PL.matrix, sparseResult = TRUE)
average.PL <- landscape.from.vector(average.PL.vector,t.vals)
plot.landscape(average.PL,t.vals)

# Second class of samples
num.repeats <- ncol(Clouds.B)

PD.list.2 <- vector("list",num.repeats)
for (c in 1 : num.repeats){
  cloud_bitmap <- Clouds.B[,c]
  V <- as.numeric(cloud_bitmap)
  M <- matrix(as.numeric(cloud_bitmap),nrow=390,ncol=294,byrow=TRUE)
  X <- sample.digital.image(M,num.pts)
  
  X.max <- max(X[,1])
  for (ff in 1:nrow(X)) {
    if (X[ff, 1] < 0.01) {
      X[ff, 1] <- X.max + 1e-3
    }
  }
  
  #plot(X, cex = 0.3, xlim = c(0,0.7))
  
  
  PH.output <- alphaComplexDiag(X)
  PD.list.2[[c]] <- PH.output[["diagram"]]
  PD.list.2[[c]][,2:3] <- sqrt(PD.list.2[[c]][,2:3])
}

DV.matrix.2 <- death.vector.matrix(PD.list.2)
average.DV.2 <- colMeans(DV.matrix.2)
plot(average.DV.2, type="l", col="blue", ylab = "Persistence")

PL.list.2 <- vector("list",num.repeats)
for (c in 1 : num.repeats)
  PL.list.2[[c]] <- t(landscape(PD.list.2[[c]],dimension=1,KK=1:100,tseq=t.vals))
PL.matrix.2 <- landscape.matrix.from.list(PL.list.2)
average.PL.vector.2 <- colMeans(PL.matrix.2, sparseResult = TRUE)
average.PL.2 <- landscape.from.vector(average.PL.vector.2,t.vals)
plot.landscape(average.PL.2,t.vals)


# Third class of samples
num.repeats <- ncol(Clouds.C)

PD.list.3 <- vector("list",num.repeats)
for (c in 1 : num.repeats){
  cloud_bitmap <- Clouds.C[,c]
  V <- as.numeric(cloud_bitmap)
  M <- matrix(as.numeric(cloud_bitmap),nrow=390,ncol=294,byrow=TRUE)
  X <- sample.digital.image(M,num.pts)
  
  X.max <- max(X[,1])
  for (ff in 1:nrow(X)) {
    if (X[ff, 1] < 0) {
      X[ff, 1] <- X.max + 1e-3
    }
  }
  
  PH.output <- alphaComplexDiag(X)
  PD.list.3[[c]] <- PH.output[["diagram"]]
  PD.list.3[[c]][,2:3] <- sqrt(PD.list.3[[c]][,2:3])
}

DV.matrix.3 <- death.vector.matrix(PD.list.3)
average.DV.3 <- colMeans(DV.matrix.3)
plot(average.DV.3, type="l", col="blue", ylab = "Persistence")

PL.list.3 <- vector("list",num.repeats)
for (c in 1 : num.repeats)
  PL.list.3[[c]] <- t(landscape(PD.list.3[[c]],dimension=1,KK=1:100,tseq=t.vals))
PL.matrix.3 <- landscape.matrix.from.list(PL.list.3)
average.PL.vector.3 <- colMeans(PL.matrix.3, sparseResult = TRUE)
average.PL.3 <- landscape.from.vector(average.PL.vector.3,t.vals)
plot.landscape(average.PL.3,t.vals)


# The difference in death vectors and persistence landscapes
difference.average.DV <- average.DV - average.DV.2
plot(difference.average.DV, type="l", col="blue", ylab="Persistence")
difference.average.PL.vector <- difference.vectors(average.PL.vector,average.PL.vector.2)
difference.average.PL <- landscape.from.vector(difference.average.PL.vector,t.vals)
plot.landscape(difference.average.PL,t.vals)

# p values for differences in the average landscapes
permutation.test(DV.matrix, DV.matrix.2, num.repeats = 1000)
permutation.test(PL.matrix, PL.matrix.2, num.repeats = 1000)

# Assemble the data
data.labels <- c(rep(1,nrow(PL.matrix)), rep(2,nrow(PL.matrix.2)), rep(3,nrow(PL.matrix.C.1)))
DV.vectors <- rbind(DV.matrix,DV.matrix.2, DV.matrix.3)
PL.vectors <- rbind(PL.matrix,PL.matrix.2, PL.matrix.3)



# SAVING - BLUE CHANNEL ------------------------------
#save(data.labels, file = "DataLabels_M2.RData")
#save(DV.vectors, file = "DVVectors_M2.RData")
#save(PL.vectors, file = "PLVectors_M2.RData")
# -------------------------------------


# LOADING IN - BLUE CHANNEL ----------------------------
# setwd("C:/Users/DELL/Desktop/UF Courses Fall 2020/Topological Data Analysis/Project")
# load("DataLabels_M2.RData")
# load("DVVectors_M2.RData")
# load("PLVectors_M2.RData")
#--------------------------------------


# Principal Components Analysis
pca.0 <- prcomp(DV.vectors,rank=10)
plot(pca.0,type="l")
plot(pca.0$x[,1:2], col=data.labels, pch=17+(2*data.labels), asp=1)
loading_vectors <- t(pca.0$rotation)
plot(loading_vectors[1,],type="l")
plot(loading_vectors[2,],type="l")
pca.1 <- prcomp(PL.vectors,rank=10)
plot(pca.1,type="l")
plot(pca.1$x[,1:2], col=data.labels, pch=17+(2*data.labels), asp=1)
loading_vectors <- t(pca.1$rotation)
plot.landscape(landscape.from.vector(loading_vectors[1,],t.vals),t.vals)
plot.landscape(landscape.from.vector(loading_vectors[2,],t.vals),t.vals)

# Support Vector Machine Classification
cost <- 10
num.folds <- 10

set.seed(1)
svm_model <- svm(DV.vectors,data.labels,scale=FALSE,type="C-classification",kernel="linear", cost=cost,cross=num.folds)
summary(svm_model)
svm_model <- svm(PL.vectors,data.labels,scale=FALSE,type="C-classification",kernel="linear", cost=cost,cross=num.folds)
summary(svm_model)



