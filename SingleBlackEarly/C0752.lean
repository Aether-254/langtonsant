import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0752 : checkSingleBlackFast (23, -11) 6215 .west (-14, 8) (-21, -16) = true := by
  decide +kernel

end LangtonsAnt
