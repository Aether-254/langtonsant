import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0741 : checkSingleBlackFast (17, -14) 6145 .west (-13, 7) (-21, -14) = true := by
  decide +kernel

end LangtonsAnt
