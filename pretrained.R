library(keras)

#model <- application_resnet50(weights = 'imagenet')
#model <- application_vgg16(weights = 'imagenet')
model <- application_inception_v3(weights = 'imagenet')

# load the image
# img_path <- "claude_299.jpg"
img_path <- "kremsater_299.jpg"
#img <- image_load(img_path, target_size = c(224,224)) # vgg, resnet
img <- image_load(img_path, target_size = c(299,299)) # inception
img
x <- image_to_array(img)
dim(x)
dim(x) <- c(1, dim(x))
#x <- imagenet_preprocess_input(x) # vgg, resnet
x <- inception_v3_preprocess_input(x) # inception

# make predictions then decode and print them
preds <- model %>% predict(x)
which.max(preds)
imagenet_decode_predictions(preds)

