import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0717 : checkSingleBlackFast (4, -13) 11472 .south (-13, 0) (-25, -14) = true := by
  decide +kernel

end LangtonsAnt
