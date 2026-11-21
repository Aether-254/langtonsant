import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell2015 : checkSingleBlackFast (-76, -49) 13344 .north (26, 18) (-52, -34) = true := by
  decide +kernel

end LangtonsAnt
