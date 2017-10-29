library(keras)
library(ggplot2)
library(tidyr)

x_train <- iris[1:120, "Petal.Length"]
y_train <- iris[1:120, "Petal.Width"]
x_test <- iris[121:150, "Petal.Length"]
y_test <- iris[121:150, "Petal.Width"]


model <- keras_model_sequential()
model %>%
  layer_dense(units = 8, input_shape = 1) %>%
  layer_activation_leaky_relu() %>%
  layer_dropout(rate = 0.2) %>%
  layer_dense(units = 1) # linear activation

model %>% summary()
# params: num_hidden weights and biases each to hidden layer, 4 weights and 1 bias to output neuron

model %>% compile(optimizer = "adam", loss = "mean_squared_error")

# dataset too small
#hist <- model %>% fit(x_train, y_train, batch_size = 10, validation_split = 0.1, epochs = 100)
hist <-
  model %>% fit(
    x_train,
    y_train,
    batch_size = 10,
    epochs = 100
  )


plot(hist)

model %>% get_weights()

model %>% evaluate(x_test, y_test)

preds <- model %>% predict(x_train)
preds_df <-
  data.frame(predictor = x_train,
             actual = y_train,
             predicted = preds)
preds_df <- preds_df %>% gather(type, value,-predictor)
ggplot(preds_df, aes(x = predictor, y = value)) + geom_point(aes(color = type))

preds <- model %>% predict(x_test)
preds_df <-
  data.frame(predictor = x_test,
             actual = y_test,
             predicted = preds)
preds_df <- preds_df %>% gather(type, value,-predictor)
ggplot(preds_df, aes(x = predictor, y = value)) + geom_point(aes(color = type))
