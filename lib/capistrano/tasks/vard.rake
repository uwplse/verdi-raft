namespace :vard do

  def vard_cluster
    cluster = roles(:node).collect do |node|
      "-node #{node.properties.name},#{node.hostname}:#{fetch(:node_port)}"
    end
    cluster.join(' ')
  end

  def vardctl_cluster
    cluster = roles(:node).collect do |node|
      "#{node.hostname}:#{fetch(:client_port)}"
    end
    cluster.join(',')
  end
  
  desc 'start vard-serialized'
  task :start do
    on roles(:node) do |node|
      execute '/sbin/start-stop-daemon',
        '--start',
        '--quiet',
        '--oknodo',
        '--make-pidfile',
        "--pidfile #{current_path}/extraction/vard-serialized/tmp/vard-serialized.pid",
        '--background',
        "--chdir #{current_path}/extraction/vard-serialized",
        '--startas /bin/bash',
        "-- -c 'exec ./vardserialized.native -me #{node.properties.name} -port #{fetch(:client_port)} -dbpath #{current_path}/extraction/vard-serialized/tmp #{vard-serialized_cluster} > log/vard-serialized.log 2>&1'"
    end
  end

  desc 'stop vard-serialized'
  task :stop do
    on roles(:node) do
      execute '/sbin/start-stop-daemon', 
        '--stop',
        '--oknodo',
        "--pidfile #{current_path}/extraction/vard/tmp/vard-serialized.pid"
    end
  end

  desc 'tail vard-serialized log'
  task :tail_log do
    on roles(:node) do
      execute :tail,
        '-n 20',
        "#{shared_path}/extraction/vard-serialized/log/vard-serialized.log"
    end
  end

  desc 'truncate vard log'
  task :truncate_log do
    on roles(:node) do
      execute :truncate,
        '-s 0',
        "#{shared_path}/extraction/vard/log/vard-serialized.log"
    end
  end

  desc 'remove command log'
  task :remove_clog do
    on roles(:node) do
      execute :rm,
        '-f',
        "#{shared_path}/extraction/vard-serialized/tmp/clog.bin"
    end
  end

  desc 'remove snapshot'
  task :remove_snapshot do
    on roles(:node) do
      execute :rm,
        '-f',
        "#{shared_path}/extraction/vard/tmp/snapshot.bin"
    end
  end

  desc 'get status'
  task :status do
    run_locally do
      info %x(python2.7 extraction/vard/bench/vardctl.py --cluster #{vardctl_cluster} status)
    end
  end

  desc 'get status remote'
  task :status_remote do
    on roles(:client) do
      execute 'python2.7',
        "#{current_path}/extraction/vard/bench/vardctl.py",
        "--cluster #{vardctl_cluster}",
        'status'
    end
  end

  desc 'put key-value pair'
  task :put do
    run_locally do
      info %x(python2.7 extraction/vard/bench/vardctl.py --cluster #{vardctl_cluster} put #{ENV['KEY']} #{ENV['VALUE']})
    end
  end

  desc 'put key-value pair remote'
  task :put_remote do
    on roles(:client) do
      execute 'python2.7',
        "#{current_path}/extraction/vard/bench/vardctl.py",
        "--cluster #{vardctl_cluster}",
        'put',
        ENV['KEY'],
        ENV['VALUE']
    end
  end

  desc 'get value for key'
  task :get do
    run_locally do
      info %x(python2.7 extraction/vard/bench/vardctl.py --cluster #{vardctl_cluster} get #{ENV['KEY']})
    end
  end

  desc 'get value for key remote'
  task :get_remote do
    on roles(:client) do
      execute 'python2.7',
        "#{current_path}/extraction/vard/bench/vardctl.py",
        "--cluster #{vardctl_cluster}",
        'get',
        ENV['KEY']
    end
  end

end
