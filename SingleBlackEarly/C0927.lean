import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0927 : checkSingleBlackFast (-11, 14) 38786 .south (9, -4) (-30, -29) = true := by
  decide +kernel

end LangtonsAnt
