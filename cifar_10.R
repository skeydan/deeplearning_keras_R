library(keras)
library(EBImage)

# Parameters --------------------------------------------------------------

batch_size <- 32
epochs <- 200


# Data Preparation --------------------------------------------------------

# airplane, automobile, bird, cat, deer, dog, frog , horse, ship, truck

cifar10 <- dataset_cifar10()
dim(cifar10$train$x)
dim(cifar10$train$y)
dim(cifar10$test$x)
dim(cifar10$test$y)

# Feature scale RGB values in test and train inputs  
x_train <- cifar10$train$x/255
x_test <- cifar10$test$x/255
y_train <- to_categorical(cifar10$train$y, num_classes = 10)
y_test <- to_categorical(cifar10$test$y, num_classes = 10)

layout(matrix(1:20, 4, 5))

for (i in 1:20) {
  img <- transpose(Image(data = x_train[i, , , ], colormode = "Color"))
  display(img, method="raster", all = TRUE)
}
        





# Defining Model ----------------------------------------------------------

# Initialize sequential model
model <- keras_model_sequential()

model %>%
  
  # Start with hidden 2D convolutional layer being fed 32x32 pixel images
  layer_conv_2d(
    filter = 32, kernel_size = c(3,3), padding = "same", 
    input_shape = c(32, 32, 3)
  ) %>%
  layer_activation("relu") %>%
  
  # Second hidden layer
  layer_conv_2d(filter = 32, kernel_size = c(3,3)) %>%
  layer_activation("relu") %>%
  
  # Use max pooling
  layer_max_pooling_2d(pool_size = c(2,2)) %>%
  layer_dropout(0.25) %>%
  
  # 2 additional hidden 2D convolutional layers
  layer_conv_2d(filter = 32, kernel_size = c(3,3), padding = "same") %>%
  layer_activation("relu") %>%
  layer_conv_2d(filter = 32, kernel_size = c(3,3)) %>%
  layer_activation("relu") %>%
  
  # Use max pooling once more
  layer_max_pooling_2d(pool_size = c(2,2)) %>%
  layer_dropout(0.25) %>%
  
  # Flatten max filtered output into feature vector 
  # and feed into dense layer
  layer_flatten() %>%
  layer_dense(512) %>%
  layer_activation("relu") %>%
  layer_dropout(0.5) %>%
  
  # Outputs from dense layer are projected onto 10 unit output layer
  layer_dense(10) %>%
  layer_activation("softmax")

opt <- optimizer_rmsprop(lr = 0.0001, decay = 1e-6)

model %>% compile(
  loss = "categorical_crossentropy",
  optimizer = opt,
  metrics = "accuracy"
)

# Training ----------------------------------------------------------------

history <- model %>% fit(
    x_train, y_train,
    batch_size = batch_size,
    epochs = epochs,
    validation_data = list(x_test, y_test),
    shuffle = TRUE
  )
plot(history)  
model %>% save_model_hdf5("cifar_10_200epochs.h5")
preds <- model %>% predict_proba(x_test)
preds[1, 1:10] %>% sum()
preds[1, 1:10] %>% which.max()
y_test[1]

model %>% evaluate(x_test, y_test) #categorical_crossentropy & accuracy
