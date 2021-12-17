pipeline {
  agent {
    dockerfile {
      label 'docker'
      additionalBuildArgs '--build-arg USER_ID=$(id -u) --build-arg GROUP_ID=$(id -g)'
    }
  }
  options { ansiColor('xterm') }
  environment { COQ_PACKAGE = 'coq-vlsm.dev' }
  stages {
    stage('Init title') {
      when { changeRequest() }
      steps { script { currentBuild.displayName = "PR ${env.CHANGE_ID}: ${env.CHANGE_TITLE}" } }
    }
    stage('Prepare and Check') {
      stages {
        stage('Prepare') {
          steps {
            sh '''
	      eval $(opam env)
              opam update -y
              opam pin add ${COQ_PACKAGE} . --yes --no-action --kind path
              opam config list
              opam repo list
              opam list
              opam install ${COQ_PACKAGE} --yes -j 8 --deps-only
            '''
          }
        }
        stage('Check') { steps { sh 'eval $(opam env) && opam install ${COQ_PACKAGE} --yes -j 8 --verbose' } }
      }
    }
    //stage('Deploy Docs') {
    //  when { branch 'master' }
    //  steps {
    //    sshagent(['2b3d8d6b-0855-4b59-864a-6b3ddf9c9d1a']) {
    //      sh '''
    //        echo "Trigger Doc Update"
    //      '''
    //    }
    //  }
    //}
  }
}
