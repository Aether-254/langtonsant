import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2147 : checkSingleBlackFast (-88, -61) 13968 .north (32, 24) (-58, -40) = true := by
  decide +kernel

end LangtonsAnt
