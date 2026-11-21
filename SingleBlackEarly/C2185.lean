import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2185 : checkSingleBlackFast (-88, -69) 22376 .north (46, 42) (-72, -34) = true := by
  decide +kernel

end LangtonsAnt
