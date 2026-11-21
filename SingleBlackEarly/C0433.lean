import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0433 : checkSingleBlackFast (17, 4) 5420 .south (-19, -6) (-25, -6) = true := by
  decide +kernel

end LangtonsAnt
