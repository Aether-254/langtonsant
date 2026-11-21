import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0647 : checkSingleBlackFast (3, -9) 11216 .south (-13, -1) (-25, -13) = true := by
  decide +kernel

end LangtonsAnt
