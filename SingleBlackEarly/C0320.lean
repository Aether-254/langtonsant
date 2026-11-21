import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0320 : checkSingleBlackFast (-1, 10) 7648 .south (-10, -5) (-18, -13) = true := by
  decide +kernel

end LangtonsAnt
