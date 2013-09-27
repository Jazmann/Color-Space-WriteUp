
angle = -0.8728;
[Y B R bin A] = colorStats( 0.114, 0.299, 0, 0, 255, 256, 0, 255, 256, 0, 255, 256);
Z = squeeze(sum(bin,2));
x(1,:) = GaussianFit( B, R, squeeze(sum(bin,2)), [1,A(3),20.5,A(2),20.5,-pi/8], 'spline', 0);
angle = angle + x(1,6);
[Y B R bin A] = colorStats( 0.114, 0.299, angle, 0, 255, 256, 0, 255, 256, 0, 255, 256);
x(2,:) = GaussianFit( B, R, squeeze(sum(bin,2)), [1,A(3),20.5,A(2),20.5,0], 'spline', 0);
angle = angle + x(2,6);
[Y B R bin A] = colorStats( 0.114, 0.299, angle, 0, 255, 256, 0, 255, 256, 0, 255, 256);
x(3,:) = GaussianFit( B, R, squeeze(sum(bin,2)), [1,A(3),20.5,A(2),20.5,0], 'spline', 0);
angle = angle + x(3,6);
[Y B R bin A] = colorStats( 0.114, 0.299, angle, 0, 255, 256, 0, 255, 256, 0, 255, 256);
x(4,:) = GaussianFit( B, R, squeeze(sum(bin,2)), [1,A(3),20.5,A(2),20.5,0], 'spline', 0);
angle = angle + x(4,6);
[Y B R bin A] = colorStats( 0.114, 0.299, angle, 0, 255, 256, 0, 255, 256, 0, 255, 256);
x(5,:) = GaussianFit( B, R, squeeze(sum(bin,2)), [1,A(3),20.5,A(2),20.5,0], 'spline', 0);
angle = angle + x(5,6);