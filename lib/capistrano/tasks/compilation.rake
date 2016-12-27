namespace :compilation do

  desc 'configure and compile'
  task :build do
    on roles(:node) do
      within release_path do
        execute './build.sh', 'vard-quick'
      end
    end
  end
  
  desc 'compile'
  task :compile do
    on roles(:node) do
      within release_path do
        execute 'make', 'vard-quick'
      end
    end
  end

end

after 'deploy:updated', 'compilation:build'
